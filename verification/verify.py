"""Build, extract and kernel-check the selected Add artifact in fresh directories."""

import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

from common import ROOT, VERIFY, run, sha, source_files

OUTPUT = VERIFY / "generated"


def source_inputs():
    paths = [ROOT / "global.json", ROOT / ".editorconfig", ROOT / ".github/workflows/verify-uint256.yml"]
    for directory in (ROOT / "src", VERIFY):
        paths.extend(source_files(directory,
                     {".cs", ".csproj", ".props", ".targets", ".lean", ".json", ".toml", ".py"}))
    paths.append(VERIFY / "lean-toolchain")
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(set(paths))}


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    OUTPUT.mkdir(exist_ok=True)
    report_path = OUTPUT / "report.json"
    # Invalidate the prior success before any command that can fail.
    report_path.unlink(missing_ok=True)
    manifest = json.loads((VERIFY / "manifests/add.json").read_text(encoding="utf-8"))
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
        artifacts = work / "artifacts"
        run(["dotnet", "build", str(ROOT / "src/Nethermind.Int256/Nethermind.Int256.csproj"),
             "-c", "Release", "--no-incremental", f"-p:ArtifactsPath={artifacts}",
             "-p:EnableZkEvm=false"], ROOT)
        assembly = artifacts / "bin/Nethermind.Int256/release/Nethermind.Int256.dll"
        if not assembly.is_file():
            raise RuntimeError("Fresh build did not produce the selected assembly")
        tools = work / "tools"
        run(["dotnet", "build", str(VERIFY / "Extractor/Extractor.csproj"), "-c", "Release",
             "--no-incremental", f"-p:ArtifactsPath={tools}", "-p:EnforceCodeStyleInBuild=true",
             "-p:GenerateDocumentationFile=true"], ROOT)
        extractor = tools / "bin/Extractor/release/Extractor.dll"
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
        generated = proof / "generated"
        run(["dotnet", str(extractor), str(assembly), str(generated)], ROOT)
        artifact = json.loads((generated / "artifact.json").read_text(encoding="utf-8"))
        assembly_hash = sha(assembly)
        if artifact["sha256"] != assembly_hash or artifact["methods"][0]["signature"] != manifest["entry"]:
            raise RuntimeError("Artifact identity mismatch")
        output = run([lake, "build", "Audit"], proof)
        audit = re.findall(r"'UInt256Proof.checked_contract' depends on axioms: \[([^]]*)\]", output)
        if len(audit) != 1:
            raise RuntimeError("Missing or ambiguous final theorem axiom audit")
        axioms = [a.strip() for a in audit[0].split(",") if a.strip()]
        if set(axioms) - set(manifest["approvedAxioms"]):
            raise RuntimeError(f"Unapproved axioms: {axioms}")
        # Neither pre-existing extraction nor an existing olean cache enters this
        # proof directory. Recheck inputs and artifact before issuing a report.
        if inputs != source_inputs() or sha(assembly) != assembly_hash:
            raise RuntimeError("Inputs changed during verification")
        commit = run(["git", "rev-parse", "HEAD"], ROOT).strip()
        status = run(["git", "status", "--porcelain"], ROOT).splitlines()
        report = {"status": "verified", "sourceCommit": commit, "sourceStatus": status,
                  "sourceInputs": inputs, "artifact": artifact, "scope": manifest,
                  "sdk": sdk, "lean": lean, "axioms": axioms,
                  "generatedProgramSha256": sha(generated / "Extracted.lean"),
                  "leanSourceSha256": {p.relative_to(VERIFY).as_posix(): sha(proof / p.relative_to(VERIFY))
                                       for p in lean_sources}}
        for name in ("Extracted.lean", "artifact.json"):
            shutil.copy2(generated / name, OUTPUT / name)
        temp_report = OUTPUT / "report.json.tmp"
        temp_report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        temp_report.replace(report_path)
        print(f"Verified {manifest['entry']} from SHA256 {assembly_hash}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
