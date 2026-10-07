"""Run the complete regression matrix from one immutable source snapshot."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.dont_write_bytecode = True
from common import BUILD_DIRECTORIES, MULTIPLY_PROFILES, PROFILES, ROOT, VERIFY, sha, api_entries, MULTIPLY_SAFETY_METHODS, BITWISE_DESCRIPTORS, BITWISE_UNARY, COMPARISON_GATES, OPERATOR_DESCRIPTORS, PRIMITIVE_COMPARISONS, coverage_plan
from common import source_inputs, copy_source


@dataclass(frozen=True)
class Job:
    id: str
    commands: tuple[tuple[str, ...], ...]


def regression_plan():
    jobs = []

    def add(name, script, *arguments):
        jobs.append(Job(name, (("verification/" + script, *arguments),)))

    add("foundation", "Runner.Tests/Verification.Tests.csproj", "foundation")
    add("safety-foundation", "Runner.Tests/Verification.Tests.csproj", "safety-foundation")
    add("safety-fixtures", "Tests/Fixtures/Safety/checks.py")
    add("safety-robustness-Add", "Runner.Tests/Verification.Tests.csproj", "robustness", "--method", "Add", "--case", "Renamed", "--case", "ReversedStore", "--safety")
    for method in sorted(MULTIPLY_SAFETY_METHODS):
        for profile in MULTIPLY_PROFILES:
            add(f"safety-{method}-{profile}", "Runner/Verification.csproj", "verify", "--method", method, "--profile", profile, "--safety")
    for profile in ("x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"):
        add(f"safety-Add-{profile}", "Runner/Verification.csproj", "verify", "--method", "Add", "--profile", profile, "--safety")
        add(f"safety-AddOverflow-{profile}", "Runner/Verification.csproj", "verify", "--method", "AddOverflow", "--profile", profile, "--safety")
    add("safety-Add-scalar", "Runner/Verification.csproj", "verify", "--method", "Add", "--profile", "scalar", "--safety")
    add("safety-Add-x64-sse42", "Runner/Verification.csproj", "verify", "--method", "Add", "--profile", "x64-sse42", "--safety")
    add("safety-Add-arm64-advsimd", "Runner/Verification.csproj", "verify", "--method", "Add", "--profile", "arm64-advsimd", "--safety")
    add("safety-AddOverflow-x64-sse42", "Runner/Verification.csproj", "verify", "--method", "AddOverflow", "--profile", "x64-sse42", "--safety")
    add("safety-AddOverflow-arm64-advsimd", "Runner/Verification.csproj", "verify", "--method", "AddOverflow", "--profile", "arm64-advsimd", "--safety")
    for method in ("Subtract", "SubtractUnderflow"):
        for profile in ("x64-sse42", "arm64-advsimd"):
            add(f"safety-{method}-{profile}", "Runner/Verification.csproj", "verify", "--method", method, "--profile", profile, "--safety")
    add("safety-EqUInt256UInt256-scalar", "Runner/Verification.csproj", "verify", "--method", "EqUInt256UInt256", "--profile", "scalar", "--safety")
    add("safety-EqUInt256UInt256-vector256", "Runner/Verification.csproj", "verify", "--method", "EqUInt256UInt256", "--profile", "x64-vector256", "--safety")
    add("safety-EqualsUInt256Ref-scalar", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt256Ref", "--profile", "scalar", "--safety")
    add("safety-NeUInt256UInt256-scalar", "Runner/Verification.csproj", "verify", "--method", "NeUInt256UInt256", "--profile", "scalar", "--safety")
    add("safety-EqualsUInt256Ref-vector256", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt256Ref", "--profile", "x64-vector256", "--safety")
    add("safety-NeUInt256UInt256-vector256", "Runner/Verification.csproj", "verify", "--method", "NeUInt256UInt256", "--profile", "x64-vector256", "--safety")
    add("safety-EqUInt256UInt256-sse41", "Runner/Verification.csproj", "verify", "--method", "EqUInt256UInt256", "--profile", "x64-sse41", "--safety")
    add("safety-EqualsUInt256Ref-sse41", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt256Ref", "--profile", "x64-sse41", "--safety")
    add("safety-NeUInt256UInt256-sse41", "Runner/Verification.csproj", "verify", "--method", "NeUInt256UInt256", "--profile", "x64-sse41", "--safety")
    add("safety-EqualsUInt256Value-scalar", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt256Value", "--profile", "scalar", "--safety")
    add("safety-EqualsUInt64-scalar", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt64", "--profile", "scalar", "--safety")
    add("safety-EqualsUInt32-scalar", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt32", "--profile", "scalar", "--safety")
    add("safety-EqualsUInt64-x64-vector256", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt64", "--profile", "x64-vector256", "--safety")
    add("safety-EqualsUInt32-x64-vector256", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt32", "--profile", "x64-vector256", "--safety")
    add("safety-EqualsInt64-scalar", "Runner/Verification.csproj", "verify", "--method", "EqualsInt64", "--profile", "scalar", "--safety")
    add("safety-EqualsInt32-scalar", "Runner/Verification.csproj", "verify", "--method", "EqualsInt32", "--profile", "scalar", "--safety")
    add("safety-EqualsInt64-x64-vector256", "Runner/Verification.csproj", "verify", "--method", "EqualsInt64", "--profile", "x64-vector256", "--safety")
    add("safety-EqualsInt32-x64-vector256", "Runner/Verification.csproj", "verify", "--method", "EqualsInt32", "--profile", "x64-vector256", "--safety")
    add("safety-EqualsUInt256Value-x64-sse41", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt256Value", "--profile", "x64-sse41", "--safety")
    add("safety-EqualsUInt256Value-x64-vector256", "Runner/Verification.csproj", "verify", "--method", "EqualsUInt256Value", "--profile", "x64-vector256", "--safety")
    for method in sorted(OPERATOR_DESCRIPTORS):
        for profile in ("scalar", "x64-vector256"):
            add(f"safety-{method}-{profile}", "Runner/Verification.csproj", "verify", "--method", method, "--profile", profile, "--safety")
    for method in sorted(PRIMITIVE_COMPARISONS):
        add(f"safety-{method}-scalar", "Runner/Verification.csproj", "verify", "--method", method, "--profile", "scalar", "--safety")
    for method in ("LeUInt64UInt256", "AddOverflow", "SubtractUnderflow", "Subtract"):
        add(f"safety-{method}-scalar", "Runner/Verification.csproj", "verify", "--method", method, "--profile", "scalar", "--safety")
    for method in ("Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"):
        for profile in ("scalar", "x64-vector256"):
            add(f"safety-{method}-{profile}", "Runner/Verification.csproj", "verify", "--method", method, "--profile", profile, "--safety")
    for method in ("Subtract", "SubtractUnderflow"):
        for profile in ("x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"):
            add(f"safety-{method}-{profile}", "Runner/Verification.csproj", "verify", "--method", method, "--profile", profile, "--safety")
    for method in sorted(set(BITWISE_DESCRIPTORS) | BITWISE_UNARY):
        for profile in ("scalar", "x64-vector256"):
            add(f"safety-{method}-{profile}", "Runner/Verification.csproj", "verify", "--method", method, "--profile", profile, "--safety")
    for method in sorted(COMPARISON_GATES):
        for profile in ("scalar", "x64-vector256", "x64-avx2", "x64-avx512"):
            add(f"safety-{method}-{profile}", "Runner/Verification.csproj", "verify", "--method", method, "--profile", profile, "--safety")
    for method in ("CompareToUInt256Ref", "CompareToUInt256Value"):
        add(f"safety-{method}-scalar", "Runner/Verification.csproj", "verify", "--method", method, "--profile", "scalar", "--safety")
    add("profile-extractor", "Tests/profile_extractor_checks.py")
    add("csharp-runner", "Runner.Tests/Verification.Tests.csproj")
    for name in ("change", "prepared", "method"):
        add("python-" + name, "Tests/" + name.replace("-", "_") + "_checks.py")
    add("python-all-checks", "Tests/all_checks_tests.py")
    add("gate-binding", "Runner.Tests/Verification.Tests.csproj", "gate-binding", "--workspace")
    for method in ("Add", "Subtract"):
        negative = ("verification/Tests/negative_checks.py",) if method == "Add" else ("verification/Runner.Tests/Verification.Tests.csproj", "subtract-negative")
        jobs.append(Job("legacy-" + method, (
            ("verification/Runner/Verification.csproj", "verify", "--method", method, "--profile", "scalar"),
            negative,
        )))
        add("robustness-" + method, "Runner.Tests/Verification.Tests.csproj", "robustness", "--method", method)
        for profile in PROFILES[1:]:
            add(f"simd-{method}-{profile}", "Tests/simd_checks.py", "--method", method,
                "--profile", profile, "--suite", "all")
    operations = ("Compare", "Bitwise", "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot",
                  "Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh")
    for operation in operations:
        if operation in ("Compare", "Bitwise"):
            for profile in ("scalar", "x64-vector256"):
                add(f"operation-{operation}-{profile}", "Runner.Tests/Verification.Tests.csproj",
                    "compare-fixtures" if operation == "Compare" else "bitwise-fixtures", "--profile", profile, "--workspace")
            continue
        script = "Bitwise/operator_checks.py" if operation in ("OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot") else "Shift/negative_checks.py"
        arguments = ("--method", operation)
        if script == "Shift/negative_checks.py":
            arguments += ("--safety",)
        for profile in ("scalar", "x64-vector256"):
            add(f"operation-{operation}-{profile}", "Tests/Fixtures/" + script,
                *arguments, "--profile", profile, "--workspace")
    equality = [name for name, entry in api_entries().items()
                if entry.get("verification", {}).get("fixtureGroup") == "Equality"]
    equal_profiles = coverage_plan(equality)
    multiply_profiles = coverage_plan(["Multiply"])
    if (len(equality) != 24 or len(equal_profiles) != 52 or len(set(equal_profiles)) != 52
            or multiply_profiles != [("Multiply", profile) for profile in MULTIPLY_PROFILES]):
        raise RuntimeError("Incomplete equality or multiplication regression selection")
    for method, profile in equal_profiles:
        add(f"equality-{method}-{profile}", "Tests/Fixtures/Equality/checks.py",
            "--method", method, "--profile", profile, "--workspace")
    for _, profile in multiply_profiles:
        add("multiply-" + profile, "Tests/Fixtures/Multiply/negative_checks.py",
            "--profile", profile, "--workspace")
    for method in ("AddOverflow", "SubtractUnderflow"):
        for profile in PROFILES:
            add(f"reporting-{method}-{profile}", "Runner.Tests/Verification.Tests.csproj", "reporting",
                "--method", method, "--profile", profile)
    if len(jobs) != 387 or len({job.id for job in jobs}) != 387:
        raise RuntimeError("Incomplete or duplicate regression matrix")
    return jobs


def ci_matrix(plan):
    """Retain every regression while staying within Actions' 256-entry limit."""
    if not plan:
        raise ValueError("Empty regression matrix")
    width = (len(plan) + 255) // 256
    return {"include": [{"batch": index // width,
                         "jobs": [job.id for job in plan[index:index + width]],
                         "timeoutMinutes": min(360, 60 * len(plan[index:index + width]))}
                        for index in range(0, len(plan), width)]}


def inputs_at(directory):
    # Execute the same source selector in the copied repository; also detects added inputs.
    code = "import sys,json;sys.path.insert(0,'verification');from common import source_inputs;print(json.dumps(source_inputs()))"
    command = [sys.executable, "-B", "-c", code]
    result = subprocess.run(command, cwd=directory,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding="utf-8")
    if result.returncode:
        details = {"command": command, "cwd": str(directory), "exitCode": result.returncode,
                   "stdout": result.stdout, "stderr": result.stderr}
        raise RuntimeError("Source input subprocess failed: " + json.dumps(details, ensure_ascii=False))
    return json.loads(result.stdout)


def require_inputs(directory, expected):
    if inputs_at(directory) != expected:
        raise RuntimeError(f"Immutable source inputs changed: {directory}")


def clone_source(source, destination):
    subprocess.run(["git", "clone", "--shared", "--no-checkout", "--quiet", str(source), str(destination)],
                   cwd=source, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def run_process(command, directory, log):
    environment = os.environ.copy()
    environment.update(DOTNET_EnableHWIntrinsic="0", DOTNET_CLI_TELEMETRY_OPTOUT="1",
                       DOTNET_SKIP_FIRST_TIME_EXPERIENCE="1", MSBuildEnableWorkloadResolver="false")
    with log.open("w", encoding="utf-8") as output:
        return subprocess.run(command, cwd=directory, env=environment,
                              stdout=output, stderr=subprocess.STDOUT).returncode


def run_job(job, seed, expected, output):
    directory = output / job.id
    directory.mkdir()
    receipt = {"job": job.id, "status": "failed", "commands": []}
    started = time.perf_counter()
    try:
        with tempfile.TemporaryDirectory(prefix="int256-check-") as temporary:
            workspace = Path(temporary) / "source"
            clone_source(seed, workspace)
            shutil.copytree(seed, workspace, dirs_exist_ok=True,
                            ignore=shutil.ignore_patterns(".git", *BUILD_DIRECTORIES))
            receipt["workspace"] = str(workspace)
            require_inputs(workspace, expected)
            for index, tokens in enumerate(job.commands):
                command = (["dotnet", "run", "--project", str(workspace / tokens[0]), "-c", "Release", "--", *tokens[1:]]
                           if tokens[0].endswith(".csproj") else
                           [sys.executable, str(workspace / tokens[0]), *tokens[1:]])
                log = directory / f"{index + 1}.log"
                command_started = time.perf_counter()
                code = run_process(command, workspace, log)
                receipt["commands"].append({"command": command, "exitCode": code,
                    "elapsedSeconds": time.perf_counter() - command_started,
                    "log": log.name, "logSha256": sha(log)})
                require_inputs(workspace, expected)
                if code:
                    raise RuntimeError(f"Regression command failed: {job.id} (exit {code})")
            receipt["status"] = "passed"
    except Exception as error:
        receipt["error"] = str(error)
        raise
    finally:
        receipt["elapsedSeconds"] = time.perf_counter() - started
        (directory / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return job.id


def run_suite(plan, selected, jobs, output, captured_inputs=None):
    if not 1 <= jobs <= 8:
        raise ValueError("Jobs must be between 1 and 8")
    if not selected or len({job.id for job in selected}) != len(selected) or any(job not in plan for job in selected):
        raise RuntimeError("Invalid or incomplete job selection")
    full = selected == plan
    output.mkdir(parents=True, exist_ok=True)
    lock = output / "full.lock"
    if full:
        descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.close(descriptor)
        (output / "report.json").unlink(missing_ok=True)
    try:
        records = Path(tempfile.mkdtemp(prefix="run-", dir=output))
        expected = source_inputs() if captured_inputs is None else captured_inputs
        if source_inputs() != expected:
            raise RuntimeError("Source inputs changed after command-plan selection")
        (records / "source-inputs.json").write_text(json.dumps(expected, indent=2) + "\n", encoding="utf-8")
        with tempfile.TemporaryDirectory(prefix="int256-check-seed-") as temporary:
            seed = Path(temporary) / "source"
            clone_source(ROOT, seed)
            copy_source(seed)
            require_inputs(seed, expected)
            if source_inputs() != expected:
                raise RuntimeError("Source inputs changed during seed capture")
            completed, errors = [], []
            with ThreadPoolExecutor(max_workers=jobs) as pool:
                pending = {pool.submit(run_job, job, seed, expected, records): job for job in selected}
                for future in as_completed(pending):
                    if future.cancelled():
                        continue
                    try:
                        completed.append(future.result())
                        print(f"PASS: {pending[future].id}", flush=True)
                    except Exception as error:
                        errors.append(error)
                        print(f"FAIL: {pending[future].id}; receipts: {records}", flush=True)
                        for queued in pending:
                            queued.cancel()
            if errors:
                raise RuntimeError(f"Regression suite failed; receipts: {records}") from errors[0]
            if set(completed) != {job.id for job in selected}:
                raise RuntimeError("Incomplete regression results")
            require_inputs(seed, expected)
        if source_inputs() != expected:
            raise RuntimeError("Source inputs changed during regression checking")
        report = {"status": "passed", "scope": "full" if full else "partial", "fullSuite": full,
                  "requiredJobs": len(plan), "selectedJobs": [job.id for job in selected],
                  "sourceInputs": expected, "receipts": [
                      {"job": job.id, "path": str((records / job.id / "receipt.json").relative_to(output)),
                       "sha256": sha(records / job.id / "receipt.json")} for job in selected]}
        target = output / "report.json" if full else records / "subset.json"
        staged = target.with_suffix(".tmp")
        staged.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        staged.replace(target)
        return target
    finally:
        if full:
            lock.unlink()


def main(arguments=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1, help="Concurrent isolated jobs (1–8)")
    parser.add_argument("--job", help="Run one exact job ID; emit only a partial receipt")
    parser.add_argument("--print-plan", action="store_true", help="Print the required command plan without running it")
    args = parser.parse_args(arguments)
    if not 1 <= args.jobs <= 8:
        parser.error("--jobs must be between 1 and 8")
    captured = source_inputs()
    plan = regression_plan()
    if source_inputs() != captured:
        raise RuntimeError("Source inputs changed during command-plan selection")
    selected = [job for job in plan if job.id == args.job] if args.job else plan
    if not selected:
        parser.error("Unknown exact job ID")
    if args.print_plan:
        print(json.dumps({"scope": "partial" if args.job else "full", "requiredJobs": len(plan),
                          "jobs": [{"id": job.id, "commands": job.commands} for job in selected],
                          "matrix": ci_matrix(selected)}, indent=2))
        return
    target = run_suite(plan, selected, args.jobs, VERIFY / "generated/all-checks", captured)
    print(f"{'Full regression suite' if not args.job else 'Partial regression job'} passed: {target}")


if __name__ == "__main__":
    main()
