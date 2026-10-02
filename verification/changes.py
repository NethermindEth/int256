"""Select a fresh production proof by comparing the selected extracted dependency graph."""

import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

from common import PROFILES, ROOT, VERIFY, run


def proof_inputs_changed(paths):
    # Only ordinary C# changes are eligible for skipping. Build configuration,
    # verification code and workflow changes always require a fresh proof.
    return any(not (path.startswith("src/") and path.endswith(".cs")) for path in paths)


def comparison_artifact(artifact):
    # DLL identity and metadata tokens can change when unrelated methods change.
    # Keep all other metadata, including layout, signatures and dependency CIL.
    artifact = {key: value for key, value in artifact.items() if key not in ("sha256", "assembly")}
    artifact["methods"] = [{key: value for key, value in method.items() if key != "token"}
                           for method in artifact["methods"]]
    return artifact


def extract(source, work, extractor, method="Add", profile="scalar"):
    artifacts = work / "artifacts"
    run(["dotnet", "build", str(source / "src/Nethermind.Int256/Nethermind.Int256.csproj"),
         "-c", "Release", "--no-incremental", f"-p:ArtifactsPath={artifacts}",
         "-p:EnableZkEvm=false"], source)
    output = work / "generated"
    run(["dotnet", str(extractor),
         str(artifacts / "bin/Nethermind.Int256/release/Nethermind.Int256.dll"),
         str(output), method, profile], source)
    artifact = json.loads((output / "artifact.json").read_text(encoding="utf-8"))
    if artifact.get("profile", {}).get("Name") != profile:
        raise RuntimeError("Change-detection extraction profile mismatch")
    entry = json.loads((VERIFY / f"manifests/{method.lower()}.json").read_text(encoding="utf-8"))["entry"]
    if artifact["methods"][artifact["entryIndex"]]["signature"] != entry:
        raise RuntimeError("Change-detection extraction method mismatch")
    return comparison_artifact(artifact), (output / "Extracted.lean").read_bytes()


def needs_proof(base, method="Add", profile="scalar"):
    if method not in ("Add", "Subtract"):
        raise ValueError("Unknown verification method")
    if profile not in PROFILES:
        raise ValueError("Unknown execution profile")
    if not base or set(base) == {"0"}:
        return True, "No comparison baseline; verifying production"
    paths = run(["git", "diff", "--no-renames", "--name-only", "-z", base, "HEAD"], ROOT).strip("\0").split("\0")
    paths = [path for path in paths if path]
    if proof_inputs_changed(paths):
        return True, "Verification or build inputs changed"
    if not paths:
        return False, "No source changes"
    manifest = json.loads((VERIFY / f"manifests/{method.lower()}.json").read_text(encoding="utf-8"))
    if run(["dotnet", "--version"], ROOT).strip() != manifest["sdk"]:
        raise RuntimeError("Unexpected .NET SDK for change detection")
    with tempfile.TemporaryDirectory(prefix="int256-changes-") as temporary:
        work = Path(temporary)
        tools = work / "tools"
        run(["dotnet", "build", str(VERIFY / "Extractor/Extractor.csproj"), "-c", "Release",
             "--no-incremental", f"-p:ArtifactsPath={tools}", "-p:EnforceCodeStyleInBuild=true",
             "-p:GenerateDocumentationFile=true"], ROOT)
        baseline = work / "baseline"
        run(["git", "clone", "--shared", "--no-checkout", "--quiet", str(ROOT), str(baseline)], ROOT)
        run(["git", "checkout", "--detach", base], baseline)
        extractor = tools / "bin/Extractor/release/Extractor.dll"
        before = extract(baseline, work / "before", extractor, method, profile)
        after = extract(ROOT, work / "after", extractor, method, profile)
    if before == after:
        return False, f"Extracted {method}/{profile}, dependencies, layout and static data are unchanged"
    return True, f"Extracted {method}/{profile}, dependencies, layout or static data changed"


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--method", choices=("Add", "Subtract"), default="Add")
    parser.add_argument("--profile", choices=PROFILES, default="scalar")
    arguments = parser.parse_args()
    if os.environ.get("VERIFY_EVENT") == "workflow_dispatch":
        required, reason = True, "Manual production verification requested"
    elif os.environ.get("VERIFY_EVENT") == "pull_request" and os.environ.get("VERIFY_BASE_BRANCH") != "main":
        required, reason = True, "PR baseline is outside the verified main branch"
    else:
        required, reason = needs_proof(os.environ.get("VERIFY_BASE", ""), arguments.method, arguments.profile)
    print(reason)
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with Path(output).open("a", encoding="utf-8") as stream:
            stream.write(f"required={str(required).lower()}\n")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with Path(summary).open("a", encoding="utf-8") as stream:
            stream.write(f"Production proof {'required' if required else 'skipped'}: {reason}.\n")


if __name__ == "__main__":
    main()
