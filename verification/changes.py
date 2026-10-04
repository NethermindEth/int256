"""Select a fresh production proof by comparing the selected extracted dependency graph."""

import argparse
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from urllib.request import Request, urlopen

from common import PROFILE_DIRECTORY, PROFILE_NAMES, PROFILES, ROOT, VERIFY, expected_profile, run
from methods import LEGACY, check_calling_convention, method_manifest, method_names


def github_json(repository, path):
    request = Request(f"https://api.github.com/repos/{repository}/{path}", headers={
        "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "int256-verification",
        **({"Authorization": "Bearer " + os.environ["GH_TOKEN"]} if os.environ.get("GH_TOKEN") else {}),
    })
    with urlopen(request, timeout=15) as response:
        return json.load(response)


def baseline_verified(base, method, profile):
    """Require an actual successful proof in the exact baseline's main push run.

    A green job that skipped its proof is insufficient. Unavailable history only
    disables the optimisation; it never disables verification.
    """
    repository = os.environ.get("GITHUB_REPOSITORY", "")
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repository) or not re.fullmatch(r"[0-9a-f]{40}", base):
        return False
    try:
        runs = github_json(repository, "actions/workflows/verify-uint256.yml/runs?"
                           f"head_sha={base}&branch=main&event=push&status=success&per_page=100")
        for run_info in runs["workflow_runs"]:
            if (run_info.get("head_sha") != base or run_info.get("head_branch") != "main"
                    or run_info.get("event") != "push" or run_info.get("status") != "completed"
                    or run_info.get("conclusion") != "success"
                    or run_info.get("path") != ".github/workflows/verify-uint256.yml"
                    or run_info.get("repository", {}).get("full_name") != repository):
                continue
            run_id, attempt = int(run_info["id"]), int(run_info["run_attempt"])
            for page in range(1, 11):
                jobs = github_json(repository, f"actions/runs/{run_id}/attempts/{attempt}/jobs?"
                                   f"per_page=100&page={page}")
                for job in jobs["jobs"]:
                    if (job.get("name") == f"Production proof ({method}, {profile})"
                            and job.get("head_sha") == base and job.get("status") == "completed"
                            and job.get("conclusion") == "success"
                            and any(step.get("name") == "Verify freshly built UInt256"
                                    and step.get("status") == "completed" and step.get("conclusion") == "success"
                                    for step in job.get("steps", []))):
                        return True
                if page * 100 >= jobs["total_count"]:
                    break
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return False
    return False


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
    manifest = method_manifest(method)
    artifacts = work / "artifacts"
    run(["dotnet", "build", str(source / "src/Nethermind.Int256/Nethermind.Int256.csproj"),
         "-c", "Release", "--no-incremental", f"-p:ArtifactsPath={artifacts}",
         "-p:EnableZkEvm=false"], source)
    output = work / "generated"
    profile_selector = profile if profile in PROFILES else "@" + str(PROFILE_DIRECTORY / f"{profile}.json")
    selection = ([method, profile] if method in LEGACY else
                 [manifest["entry"], profile_selector, str(VERIFY / "manifests/api-coverage.json")])
    run(["dotnet", str(extractor),
         str(artifacts / "bin/Nethermind.Int256/release/Nethermind.Int256.dll"),
         str(output), *selection], source)
    artifact = json.loads((output / "artifact.json").read_text(encoding="utf-8"))
    if artifact.get("profile") != expected_profile(profile):
        raise RuntimeError("Change-detection extraction profile mismatch")
    if artifact["methods"][artifact["entryIndex"]]["signature"] != manifest["entry"]:
        raise RuntimeError("Change-detection extraction method mismatch")
    if method not in LEGACY:
        check_calling_convention(artifact["methods"][artifact["entryIndex"]], manifest["callingConvention"])
    return comparison_artifact(artifact), (output / "Extracted.lean").read_bytes()


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
