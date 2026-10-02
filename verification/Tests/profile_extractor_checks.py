"""Versioned infrastructure fixtures for profile and static-data extraction.

These checks validate rejection classes and artifact binding, not arithmetic
correctness. Production and semantic-negative proofs remain separate gates.
"""

import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import PROFILES, ROOT, VERIFY, run, sha


def build(project, artifacts, *properties, succeeds=True):
    return run(["dotnet", "build", str(project), "-c", "Release", "--nologo",
                f"-p:ArtifactsPath={artifacts}", "-p:EnforceCodeStyleInBuild=true",
                "-p:GenerateDocumentationFile=true", *properties], ROOT, succeeds=succeeds)


def require_rejection(output, diagnostic):
    if diagnostic not in output:
        raise RuntimeError(f"Fixture failed outside the expected extractor rejection: {diagnostic}")
    if any(marker in output for marker in ("BadImageFormatException", "OutOfMemoryException",
                                          "StackOverflowException", "maximum number of heartbeats")):
        raise RuntimeError("Malformed fixture or resource exhaustion is not the expected rejection")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    project = VERIFY / "Tests/Fixtures/Profiles/Nethermind.Int256.csproj"
    metadata_project = VERIFY / "Tests/ProfileMetadataFixture/ProfileMetadataFixture.csproj"
    with tempfile.TemporaryDirectory(prefix="int256-profile-extractor-") as temporary:
        work = Path(temporary)
        build(VERIFY / "Extractor/Extractor.csproj", work / "extractor")
        extractor = work / "extractor/bin/Extractor/release/Extractor.dll"
        build(metadata_project, work / "metadata")
        metadata = work / "metadata/bin/ProfileMetadataFixture/release/ProfileMetadataFixture.dll"
        assemblies = {}

        def fixture(name):
            if name not in assemblies:
                artifacts = work / name
                build(project, artifacts, f"-p:FixtureName={name}")
                assemblies[name] = artifacts / "bin/Nethermind.Int256/release/Nethermind.Int256.dll"
            return assemblies[name]

        def extract(assembly, label, profile="scalar", rejection=None):
            output = work / "generated" / label / profile
            text = run(["dotnet", str(extractor), str(assembly), str(output), "Add", profile],
                       ROOT, succeeds=rejection is None)
            if rejection is not None:
                require_rejection(text, rejection)
                return None
            artifact = json.loads((output / "artifact.json").read_text(encoding="utf-8"))
            if artifact["profile"]["Name"] != profile or artifact["sha256"] != sha(assembly):
                raise RuntimeError("Profile or assembly identity mismatch in fresh extraction")
            return output, artifact

        known = fixture("KnownFeature")
        for profile in PROFILES:
            output, artifact = extract(known, "known", profile)
            program = (output / "Extracted.lean").read_text(encoding="utf-8")
            if ".feature .avx2" not in program or ".featureDisabled" in program:
                raise RuntimeError("Feature getter was not preserved as a typed operation")
            probe = next(m for m in artifact["methods"] if "::Probe(" in m["signature"])
            coverage = next(c for c in artifact["coverage"] if c["method"] == probe["signature"])
            instructions = probe["instructions"]
            index = next(i for i, op in enumerate(instructions) if op["operand"] ==
                         "System.Boolean System.Runtime.Intrinsics.X86.Avx2::get_IsSupported()")
            branch = instructions[index + 1]
            if branch["opcode"] not in ("brfalse", "brfalse.s", "brtrue", "brtrue.s"):
                raise RuntimeError("Versioned feature fixture branch structure changed")
            enabled = artifact["profile"]["Avx2"]
            taken = enabled == branch["opcode"].startswith("brtrue")
            selected = int(branch["operand"]) if taken else instructions[index + 2]["Offset"]
            if selected not in coverage["reachable"]:
                raise RuntimeError("Reachability disagrees with the fixed execution profile")
        print("PASS: every named profile preserves and consistently evaluates the exact getter")

        # A portable Vector API needs no ISA guard. In contrast, even an
        # arithmetic identity implemented with an ISA-specific instruction must
        # be unreachable on every profile that lacks the required capability.
        for profile in PROFILES:
            extract(fixture("PortableVector"), "portable", profile)
            supported = profile.startswith("x64-avx512")
            extract(fixture("UnguardedAvx512"), "unguarded", profile,
                    None if supported else "Reachable intrinsic lacks Avx512FVL")
            extract(fixture("WeakAvx512Guard"), "weak-guard", profile,
                    "Reachable intrinsic lacks Avx512FVL" if profile.startswith("x64-avx2") else None)
            extract(fixture("MergedAvx512Guard"), "merged-guard", profile,
                    None if supported else "Reachable intrinsic lacks Avx512FVL")
        print("PASS: portable vectors accepted; absent/weak/data-dependent ISA guards rejected")

        lake = shutil.which("lake")
        if lake is None:
            raise RuntimeError("Pinned Lean/lake required to check emitted guard/profile certificates")
        run([lake, "build", "+CIL.ProfileEquivalence:olean", "+CIL.SymbolicExecution:olean"], VERIFY)
        guarded = fixture("GuardedAvx512")
        guarded_variants = [("guarded", guarded), ("inherited", fixture("InheritedAvx2Guard"))]
        for mode in ("guard-cached", "guard-negated", "guard-and"):
            changed = work / f"{mode}.dll"
            run(["dotnet", str(metadata), mode, str(guarded), str(changed)], ROOT)
            if sha(changed) == sha(guarded):
                raise RuntimeError("Guard fixture did not change the artifact")
            guarded_variants.append((mode, changed))
        for label, assembly in guarded_variants:
            for profile in PROFILES:
                output, artifact = extract(assembly, label, profile)
                run([lake, "env", "lean", str(output / "Extracted.lean")], VERIFY)
                live = {c["method"]: set(c["reachable"]) for c in artifact["coverage"]}
                calls = [op for method in artifact["methods"] for op in method["instructions"]
                         if op["Offset"] in live[method["signature"]] and op["opcode"] == "call"
                         and ("::TernaryLogic(" in str(op["operand"]) or "::Permute4x64(" in str(op["operand"]))]
                if bool(calls) != profile.startswith("x64-avx512"):
                    raise RuntimeError("Fixed guard did not select the expected intrinsic path")
        print("PASS: cached, negated, compound and inherited ISA guards with checked family certificates")

        cases = {
            "UnknownFeature": ("scalar", "Unclassified feature getter"),
            "UnclassifiedFeature": ("scalar", "New feature query invalidates the declared behaviour classification"),
            "UnsupportedIntrinsic": ("x64-avx2", "Unsupported external dependency"),
            "UnsupportedUnsafe": ("x64-avx2", "Unsupported external dependency"),
            "StaticInitializer": ("x64-avx2", "Unmodelled static initialisation"),
            "GenericHelper": ("scalar", "Unsupported method metadata"),
        }
        for name, (profile, diagnostic) in cases.items():
            extract(fixture(name), name, profile, diagnostic)
            print(f"PASS: {name} rejected for its expected infrastructure reason")
        extract(known, "invalid-profile", "missing-profile", "Unknown execution profile")
        text = build(project, work / "unknown-fixture", "-p:FixtureName=MissingFixture", succeeds=False)
        require_rejection(text, "Unknown profile fixture")

        static = fixture("StaticData")
        baseline_dir, baseline = extract(static, "static", "x64-avx2")
        if len(baseline["staticData"]) != 1 or baseline["staticData"][0]["bytes"] != (
                "0100000000000000020000000000000003000000000000000400000000000000"):
            raise RuntimeError("Extraction did not bind the actual versioned RVA data")
        metadata_cases = {
            "feature-scope": (known, "scalar", "Unsupported feature getter"),
            "generic-feature": (known, "scalar", "Unsupported feature getter"),
            "intrinsic-scope": (static, "x64-avx2", "Unsupported type identity"),
            "generic-argument-scope": (static, "x64-avx2", "Unsupported type identity"),
            "vector-class-encoding": (static, "x64-avx2", "Unsupported type identity"),
            "operand-type-scope": (static, "x64-avx2", "Unsupported type identity"),
            "field-type-scope": (known, "scalar", "Unsupported type identity"),
            "getter-return-scope": (known, "scalar", "Unsupported type identity"),
            "uint256-size": (static, "x64-avx2", "Unsupported UInt256 layout"),
            "uint256-base-scope": (static, "x64-avx2", "Unsupported UInt256 layout"),
            "static-base-scope": (static, "x64-avx2", "Unsupported static data or initialisation"),
            "static-memberref-scope": (static, "x64-avx2", "Unsupported static data or initialisation"),
            "static-mutable": (static, "x64-avx2", "Unsupported static data or initialisation"),
            "static-initializer": (static, "x64-avx2", "Unsupported static data or initialisation"),
        }
        for mode, (source, profile, diagnostic) in metadata_cases.items():
            changed = work / f"{mode}.dll"
            run(["dotnet", str(metadata), mode, str(source), str(changed)], ROOT)
            if sha(changed) == sha(source):
                raise RuntimeError("Metadata fixture did not change the artifact")
            extract(changed, mode, profile, diagnostic)
            print(f"PASS: {mode} rejected for its expected infrastructure reason")

        changed = work / "static-byte.dll"
        run(["dotnet", str(metadata), "static-byte", str(static), str(changed)], ROOT)
        changed_dir, changed_artifact = extract(changed, "static-byte", "x64-avx2")
        if (changed_artifact["staticData"][0]["bytes"] != "00" + baseline["staticData"][0]["bytes"][2:]
                or sha(changed_dir / "Extracted.lean") == sha(baseline_dir / "Extracted.lean")):
            raise RuntimeError("Changed actual RVA bytes were replaced or omitted from the program")
        print("PASS: changed immutable bytes change both artifact data and the extracted program")


if __name__ == "__main__":
    main()
