"""Select a fresh production proof by comparing the selected extracted dependency graph."""

import argparse
import base64
import json
import os
from pathlib import Path
import sys
import tempfile

from common import _runner_request
from common import PROFILE_NAMES, PROFILES, ROOT, VERIFY, run, LEGACY, method_manifest, method_names


def baseline_verified(base, method, profile):
    return json.loads(_runner_request(["baseline-evidence", "--json"],
        {"baseline": base, "method": method, "profile": profile,
         "repository": os.environ.get("GITHUB_REPOSITORY", "")}, cache=False))


def proof_inputs_changed(paths):
    # Only ordinary C# changes are eligible for skipping. Build configuration,
    # verification code and workflow changes always require a fresh proof.
    return any(not (path.startswith("src/") and path.endswith(".cs")) for path in paths)


def extract(source, work, extractor, method="Add", profile="scalar"):
    result = json.loads(_runner_request(["change-extract", "--json"],
        {"source": str(source), "work": str(work), "extractor": str(extractor),
         "method": method, "profile": profile}, cache=False, show_output=True))
    return result["artifact"], base64.b64decode(result["program"])


def needs_proof(base, method="Add", profile="scalar"):
    if method not in method_names():
        raise ValueError("Unknown verification method")
    if profile not in PROFILE_NAMES or (method in LEGACY and profile not in PROFILES):
        raise ValueError("Unknown execution profile")
    manifest = method_manifest(method)
    if not base or set(base) == {"0"}:
        return True, "No comparison baseline; verifying production"
    paths = run(["git", "diff", "--no-renames", "--name-only", "-z", base, "HEAD"], ROOT).strip("\0").split("\0")
    paths = [path for path in paths if path]
    if proof_inputs_changed(paths):
        return True, "Verification or build inputs changed"
    if not baseline_verified(base, method, profile):
        return True, f"No successful baseline proof evidence for {method}/{profile}; verifying production"
    if not paths:
        return False, "No source changes; exact baseline proof passed"
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
    parser.add_argument("--method", choices=method_names(), default="Add")
    parser.add_argument("--profile", choices=PROFILE_NAMES, default="scalar")
    arguments = parser.parse_args()
    if arguments.method in LEGACY and arguments.profile not in PROFILES:
        parser.error("Additional profiles require an exact selected API contract")
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
