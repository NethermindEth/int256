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
from common import BUILD_DIRECTORIES, MULTIPLY_PROFILES, PROFILES, ROOT, VERIFY, sha, api_entries, coverage_plan
from common import source_inputs, copy_source, _runner_request


@dataclass(frozen=True)
class Job:
    id: str
    commands: tuple[tuple[str, ...], ...]


def regression_plan():
    return [Job(job["id"], tuple(tuple(command) for command in job["commands"]))
            for job in json.loads(_runner_request(["regression-plan"]))]


def ci_matrix(plan):
    return json.loads(_runner_request(["regression-matrix", "--json"], [job.id for job in plan]))


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
