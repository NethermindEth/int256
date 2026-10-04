"""Build, extract and kernel-check the selected UInt256 artifact in fresh directories."""

import argparse
import copy
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import time

from common import PROFILE_DIRECTORY, PROFILE_NAMES, PROFILES, ROOT, SEMANTICS_VERSION, VERIFY, expected_profile, generated_directory, run, sha, source_files
from simd_fixtures import CASES as SIMD_CASES
from methods import LEGACY, api_entries, check_calling_convention, method_manifest, method_names
from gate_templates import audit_module, bound_audit_names

def run_stage(command, cwd, stage):
    try:
        return run(command, cwd)
    except RuntimeError as error:
        raise RuntimeError(f"{stage} failure: {error}") from error


def theorem_audits(output, names, approved):
    audits = {}
    for name in names:
        matches = re.findall(rf"'{re.escape(name)}' (?:depends on axioms: \[([\w.,\s]*)\]|does not depend on any axioms)", output)
        if len(matches) != 1:
            raise RuntimeError(f"Missing or ambiguous theorem axiom audit: {name}")
        axioms = [item.strip() for item in matches[0].split(",") if item.strip()]
        if len(axioms) != len(set(axioms)) or set(axioms) - set(approved):
            raise RuntimeError(f"Unapproved or duplicate axioms for {name}: {axioms}")
        audits[name] = axioms
    return audits


def audit_names(method):
    if method not in LEGACY:
        gate = method_manifest(method)["verification"]
        return gate["auditedTheorems"] + ([] if "template" in gate else bound_audit_names(api_entries()[method]))
    theorem, certificate = {"Add": ("checked_contract", "checked_add_family_certificate"),
                            "Subtract": ("checked_subtract_contract", "checked_subtract_family_certificate")}[method]
    return [f"UInt256Proof.{theorem}", f"UInt256Proof.{theorem}_family",
            f"UInt256Proof.{certificate}", "UInt256Proof.checked_profile_representative"]


def source_inputs():
    paths = [ROOT / "global.json", ROOT / ".editorconfig"]
    paths.extend(p for p in ROOT.iterdir() if p.is_file() and p.suffix.lower() in {".props", ".targets", ".config"})
    paths.extend((ROOT / ".github/workflows").glob("verify-uint256*.yml"))
    for directory in (ROOT / "src", VERIFY):
        paths.extend(source_files(directory,
                     {".cs", ".csproj", ".props", ".targets", ".lean", ".in", ".json", ".toml", ".py"}))
    paths.append(VERIFY / "lean-toolchain")
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(set(paths))}


def check_proof_snapshot(proof, relative_paths, inputs):
    hashes = {str(path).replace("\\", "/"): sha(proof / path) for path in relative_paths}
    if any(inputs.get(f"verification/{path}") != digest for path, digest in hashes.items()):
        raise RuntimeError("Proof snapshot does not match captured source inputs")
    return hashes


def build_artifact(project, work, method, fixture=None, simd_fixture=False, fixture_name=None):
    inputs = source_inputs()
    stages = {}
    artifacts = work / "artifacts"
    build = ["dotnet", "build", str(project), "-c", "Release", "--no-incremental",
             f"-p:ArtifactsPath={artifacts}", "-p:EnableZkEvm=false"]
    if fixture:
        build += [f"-p:FixtureMethod={method}", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]
        build += ([f"-p:FixtureCase={fixture_name}"] if simd_fixture else [f"-p:FixtureSource={fixture}"])
    stage_started = time.perf_counter()
    run_stage(build, ROOT, "Fixture maintenance/build" if fixture else "Production build")
    stages["assemblyBuildSeconds"] = time.perf_counter() - stage_started
    assembly = artifacts / "bin/Nethermind.Int256/release/Nethermind.Int256.dll"
    if not assembly.is_file():
        raise RuntimeError("Fresh build did not produce the selected assembly")
    tools = work / "tools"
    stage_started = time.perf_counter()
    run(["dotnet", "build", str(VERIFY / "Extractor/Extractor.csproj"), "-c", "Release",
         "--no-incremental", f"-p:ArtifactsPath={tools}", "-p:EnforceCodeStyleInBuild=true",
         "-p:GenerateDocumentationFile=true"], ROOT)
    stages["extractorBuildSeconds"] = time.perf_counter() - stage_started
    extractor = tools / "bin/Extractor/release/Extractor.dll"
    if inputs != source_inputs():
        raise RuntimeError("Inputs changed during artifact build")
    return {"assembly": assembly, "extractor": extractor, "timings": stages,
            "sourceInputs": inputs, "assemblySha256": sha(assembly), "extractorSha256": sha(extractor),
            "project": project.resolve(), "fixture": fixture_name if fixture else None}


def validate_bundle(bundle, inputs, production=False):
    if bundle["sourceInputs"] != inputs or inputs != source_inputs():
        raise RuntimeError("Shared artifact build has stale source inputs")
    if sha(bundle["assembly"]) != bundle["assemblySha256"] or sha(bundle["extractor"]) != bundle["extractorSha256"]:
        raise RuntimeError("Artifact build identity changed")
    if production and (bundle["project"] != (ROOT / "src/Nethermind.Int256/Nethermind.Int256.csproj").resolve()
                       or bundle["fixture"] is not None):
        raise RuntimeError("A shared production build cannot verify fixtures")


def main(argv=None, prepared=None):
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--method", choices=method_names(), default="Add", help="Exact selected entry to verify")
    parser.add_argument("--profile", choices=PROFILE_NAMES, default="scalar",
                        help="Fixed execution feature profile; scalar preserves the original default")
    fixtures = parser.add_mutually_exclusive_group()
    fixtures.add_argument("--fixture", help="Versioned scalar fixture name (without .cs)")
    fixtures.add_argument("--simd-fixture", help="Registered SIMD fixture case")
    arguments = parser.parse_args(argv)
    output_directory = generated_directory(arguments.method, arguments.profile)
    output_directory.mkdir(parents=True, exist_ok=True)
    report_path = output_directory / "report.json"
    # Invalidate the prior success before any command that can fail.
    report_path.unlink(missing_ok=True)
    (VERIFY / "generated/coverage.json").unlink(missing_ok=True)
    (generated_directory(arguments.method) / "coverage.json").unlink(missing_ok=True)
    started = time.perf_counter()
    stages = {}
    manifest = method_manifest(arguments.method)
    gate = manifest.get("verification")
    if not gate and arguments.profile not in PROFILES:
        raise RuntimeError("Additional profiles require an exact API profile-agreement audit gate")
    if gate and arguments.simd_fixture:
        raise RuntimeError("Selected API does not use the legacy SIMD fixture project")
    fixture_group = gate.get("fixtureGroup", arguments.method) if gate else arguments.method
    fixture_directory = VERIFY / "Tests/Fixtures" / ("SIMD" if arguments.simd_fixture else fixture_group)
    fixture_name = arguments.simd_fixture or arguments.fixture
    fixture_source = (gate.get("fixtureSources", {}).get(fixture_name, f"{fixture_name}.cs")
                      if gate else f"{fixture_name}.cs")
    fixture = (fixture_directory / "Cases.props" if arguments.simd_fixture else
               fixture_directory / fixture_source if fixture_name else None)
    if arguments.simd_fixture and fixture_name not in SIMD_CASES:
        raise RuntimeError(f"Unknown SIMD fixture: {fixture_name}")
    if gate and fixture_name and fixture_name not in gate.get("fixtureCases", []):
        raise RuntimeError(f"Unknown fixture for selected API: {fixture_name}")
    if fixture is not None and (fixture.parent != fixture_directory or not fixture.is_file()):
        raise RuntimeError("Fixture maintenance failure: requested versioned fixture is absent")
    project = (fixture_directory / "Nethermind.Int256.csproj" if gate and fixture else
               VERIFY / "Tests/Fixtures/SIMD/Nethermind.Int256.csproj" if arguments.simd_fixture else
               VERIFY / "Tests/Fixtures/Nethermind.Int256.csproj" if fixture else
               ROOT / "src/Nethermind.Int256/Nethermind.Int256.csproj")
    inputs = source_inputs()
    sdk = run(["dotnet", "--version"], ROOT).strip()
    if sdk != manifest["sdk"]:
        raise RuntimeError(f"SDK {manifest['sdk']} required; got {sdk}")
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Lean 4.34.1 / lake must be on PATH")
    lean = run([lake, "env", "lean", "--version"], VERIFY).strip()
    if not re.search(r"version 4\.34\.1\b", lean):
        raise RuntimeError(f"Unexpected Lean toolchain: {lean}")
    with tempfile.TemporaryDirectory(prefix="int256-verify-") as temporary:
        work = Path(temporary)
        bundle = prepared or build_artifact(project, work, arguments.method, fixture,
                                            bool(arguments.simd_fixture or gate), fixture_name)
        if prepared and fixture:
            raise RuntimeError("A shared production build cannot verify fixtures")
        validate_bundle(bundle, inputs, production=bool(prepared))
        assembly, extractor = bundle["assembly"], bundle["extractor"]
        if prepared:
            stages["sharedAssemblyBuild"] = True
        else:
            stages.update(bundle["timings"])
        proof = work / "proof"
        proof.mkdir()
        # Copy source modules recursively, never generated programs or compiled caches.
        lean_sources = sorted(source_files(VERIFY, {".lean"}))
        for source in lean_sources:
            target = proof / source.relative_to(VERIFY)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        for name in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(VERIFY / name, proof / name)
        copied_paths = [p.relative_to(VERIFY) for p in lean_sources] + [Path("lakefile.toml"), Path("lean-toolchain")]
        check_proof_snapshot(proof, copied_paths, inputs)
        generated = proof / "generated"
        stage_started = time.perf_counter()
        profile_selector = ("@" + str(PROFILE_DIRECTORY / f"{arguments.profile}.json")
                            if arguments.profile not in PROFILES else arguments.profile)
        selection = ([manifest["entry"], profile_selector, str(VERIFY / "manifests/api-coverage.json")]
                     if gate else [arguments.method, arguments.profile])
        run(["dotnet", str(extractor), str(assembly), str(generated), *selection], ROOT)
        stages["extractionSeconds"] = time.perf_counter() - stage_started
        artifact = json.loads((generated / "artifact.json").read_text(encoding="utf-8"))
        assembly_hash = sha(assembly)
        if artifact["sha256"] != assembly_hash or artifact["methods"][artifact["entryIndex"]]["signature"] != manifest["entry"]:
            raise RuntimeError("Artifact identity mismatch")
        if gate:
            check_calling_convention(artifact["methods"][artifact["entryIndex"]], manifest["callingConvention"])
        if artifact.get("profile") != expected_profile(arguments.profile):
            raise RuntimeError("Extracted feature profile does not match the requested profile")
        generated_gate_hash = None
        if gate:
            target = proof / "UInt256/Methods/SelectedGate.lean"
            if target.exists():
                raise RuntimeError("Generated typed audit would overwrite handwritten source")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(audit_module(api_entries()[arguments.method]), encoding="utf-8", newline="\n")
            generated_gate_hash = sha(target)
        audit_target = "+UInt256.Methods.SelectedGate:olean" if gate else "Audit" if arguments.method == "Add" else "SubtractAudit"
        stage_started = time.perf_counter()
        output = run_stage([lake, "build", audit_target], proof, "Proof checking")
        stages["freshKernelBuildSeconds"] = time.perf_counter() - stage_started
        audited_names = audit_names(arguments.method)
        audits = theorem_audits(output, audited_names, manifest["approvedAxioms"])
        axioms = audits[audited_names[0]]
        # Neither pre-existing extraction nor an existing olean cache enters this
        # proof directory. Recheck inputs and artifact before issuing a report.
        validate_bundle(bundle, inputs, production=bool(prepared))
        copied_hashes = check_proof_snapshot(proof, copied_paths, inputs)
        if generated_gate_hash is not None and sha(target) != generated_gate_hash:
            raise RuntimeError("Generated typed audit changed during proof checking")
        commit = run(["git", "rev-parse", "HEAD"], ROOT).strip()
        status = run(["git", "status", "--porcelain"], ROOT).splitlines()
        scope = copy.deepcopy(manifest)
        scope["environment"]["selectedProfile"] = arguments.profile
        report = {"status": "verified", "sourceCommit": commit, "sourceStatus": status,
                  "sourceInputs": inputs, "artifact": artifact, "scope": scope,
                  "executionProfile": artifact["profile"],
                  "semanticsVersion": SEMANTICS_VERSION,
                  "extractorSha256": bundle["extractorSha256"],
                  "auditedTheorems": audited_names, "axiomAudits": audits,
                  "coverage": {"kind": gate["profileCoverage"] if gate else "feature-family", "aggregateChecked": False,
                               "representative": arguments.profile,
                               "condition": ("Every valid profile; kernel-checked independence of actual program operations"
                                             if gate and gate.get("allProfiles") else
                                             "Valid profile agreeing on actual program feature queries and operation availability"
                                             if gate else "Valid profile with the same checked FeatureClass")},
                  "source": {"kind": "fixture" if fixture else "production",
                             "project": project.relative_to(ROOT).as_posix(),
                             "fixture": fixture.relative_to(ROOT).as_posix() if fixture else None,
                             **({"case": fixture_name} if arguments.simd_fixture or (gate and fixture) else {})},
                  "sdk": sdk, "lean": lean, "axioms": axioms,
                  "timings": {**stages, "totalSeconds": time.perf_counter() - started},
                  "summaryRejections": re.findall(r"Optional summary candidate (\S+) was not proved; using raw execution \(([^)]+)\)", output),
                  "generatedProgramSha256": sha(generated / "Extracted.lean"),
                  "generatedGateSha256": generated_gate_hash,
                  "leanSourceSha256": {p.relative_to(VERIFY).as_posix(): copied_hashes[p.relative_to(VERIFY).as_posix()]
                                       for p in lean_sources}}
        for name in ("Extracted.lean", "artifact.json"):
            shutil.copy2(generated / name, output_directory / name)
        if generated_gate_hash is not None:
            shutil.copy2(proof / "UInt256/Methods/SelectedGate.lean", output_directory / "SelectedGate.lean")
        temp_report = output_directory / "report.json.tmp"
        temp_report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        temp_report.replace(report_path)
        print(f"Verified {manifest['entry']} from SHA256 {assembly_hash}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
