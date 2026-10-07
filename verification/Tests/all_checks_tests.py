"""Check comprehensive regression selection, isolation and fail-closed receipts."""

from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import threading
import unittest
from unittest.mock import patch

import all_checks as checks

INPUTS_AT = checks.inputs_at


class PlanChecks(unittest.TestCase):
    def test_ci_batches_retain_every_job_at_matrix_boundary(self):
        for count in (1, 256, 257, 387):
            with self.subTest(count=count):
                plan = [checks.Job(f"job-{i}", ()) for i in range(count)]
                batches = checks.ci_matrix(plan)["include"]
                self.assertLessEqual(len(batches), 256)
                self.assertEqual([name for batch in batches for name in batch["jobs"]],
                                 [job.id for job in plan])
                self.assertTrue(all(batch["jobs"] for batch in batches))
                self.assertTrue(all(batch["timeoutMinutes"] == 60 * len(batch["jobs"])
                                    for batch in batches))
        with self.assertRaises(ValueError):
            checks.ci_matrix([])

    def test_exact_required_matrix(self):
        plan = checks.regression_plan()
        by_id = {job.id: job for job in plan}
        self.assertEqual(by_id["profile-extractor"].commands, (("verification/Runner.Tests/Verification.Tests.csproj", "profile-extractor"),))
        self.assertEqual(by_id["safety-fixtures"].commands, (("verification/Runner.Tests/Verification.Tests.csproj", "safety-fixtures"),))
        self.assertEqual(len(by_id), 387)
        expected_counts = {"equality-": 52, "multiply-": 14, "simd-": 12,
                           "operation-": 24, "reporting-": 14, "legacy-": 2, "robustness-": 2}
        for prefix, count in expected_counts.items():
            self.assertEqual(sum(name.startswith(prefix) for name in by_id), count)
        expected_foundations = {"csharp-runner", "foundation", "profile-extractor", "gate-binding", "python-all-checks", "safety-robustness-Add",
                               "safety-foundation", "safety-fixtures", "safety-Add-scalar", "safety-Add-x64-avx2", "safety-Add-x64-avx2-bmi1", "safety-EqUInt256UInt256-scalar",
                               "safety-Add-x64-sse42", "safety-Add-arm64-advsimd", "safety-AddOverflow-arm64-advsimd", "safety-AddOverflow-x64-sse42", "safety-EqualsUInt256Ref-scalar",
                               "safety-NeUInt256UInt256-scalar",
                               "safety-EqUInt256UInt256-vector256",
                               "safety-EqualsUInt256Value-scalar", "safety-EqualsUInt256Value-x64-sse41",
                               "safety-EqualsUInt256Value-x64-vector256", "safety-EqualsUInt64-scalar",
                               "safety-EqualsUInt32-scalar",
                               "safety-EqualsUInt64-x64-vector256", "safety-EqualsUInt32-x64-vector256",
                               "safety-EqualsInt64-scalar", "safety-EqualsInt32-scalar",
                               "safety-EqualsInt64-x64-vector256", "safety-EqualsInt32-x64-vector256",
                               "safety-EqUInt256UInt256-sse41", "safety-EqualsUInt256Ref-sse41", "safety-NeUInt256UInt256-sse41",
                               "safety-EqualsUInt256Ref-vector256", "safety-NeUInt256UInt256-vector256",
                               *("python-" + name for name in ("change", "prepared", "method"))}
        expected_foundations.update(f"safety-{method}-{profile}"
                                    for method in ("Multiply", "MultiplyInstance", "OperatorMultiplyUInt256UInt256",
                                                   "OperatorMultiplyUInt256UInt32", "OperatorMultiplyUInt32UInt256",
                                                   "OperatorMultiplyUInt256UInt64", "OperatorMultiplyUInt64UInt256")
                                    for profile in checks.MULTIPLY_PROFILES)
        expected_foundations.update(f"safety-{method}-{profile}"
                                    for method in ("LeftShift", "RightShift", "OperatorLsh", "OperatorRsh")
                                    for profile in ("scalar", "x64-vector256"))
        expected_foundations.update(f"safety-{method}-{profile}"
                                    for method in ("Subtract", "SubtractUnderflow")
                                    for profile in ("x64-sse42", "arm64-advsimd"))
        for scalar in ("Int32", "UInt32", "Int64", "UInt64"):
            for operands in ("UInt256" + scalar, scalar + "UInt256"):
                for polarity in ("Eq", "Ne"):
                    for profile in ("scalar", "x64-vector256"):
                        expected_foundations.add(f"safety-{polarity}{operands}-{profile}")
                for relation in ("Lt", "Le", "Gt", "Ge"):
                    expected_foundations.add(f"safety-{relation}{operands}-scalar")
        expected_foundations.update({"safety-Lsh-scalar", "safety-Rsh-scalar", "safety-Lsh-x64-vector256", "safety-Rsh-x64-vector256", "safety-AddOverflow-scalar", "safety-AddOverflow-x64-avx2", "safety-SubtractUnderflow-scalar", "safety-Subtract-scalar", "safety-Subtract-x64-avx2", "safety-Subtract-x64-avx2-bmi1",
                                     "safety-SubtractUnderflow-x64-avx2", "safety-SubtractUnderflow-x64-avx2-bmi1"})
        expected_foundations.update(f"safety-{method}-{profile}"
                                    for method in ("Add", "Subtract", "SubtractUnderflow")
                                    for profile in ("x64-avx512", "x64-avx512-bmi1"))
        expected_foundations.update(f"safety-AddOverflow-{profile}"
                                    for profile in ("x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"))
        for method in ("Xor", "And", "Or", "Not", "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot"):
            for profile in ("scalar", "x64-vector256"):
                expected_foundations.add(f"safety-{method}-{profile}")
        for relation in ("Lt", "Gt", "Le", "Ge"):
            for profile in ("scalar", "x64-vector256", "x64-avx2", "x64-avx512"):
                expected_foundations.add(f"safety-{relation}UInt256UInt256-{profile}")
        for method in ("CompareToUInt256Ref", "CompareToUInt256Value"):
            expected_foundations.add(f"safety-{method}-scalar")
        for name in expected_foundations:
            if name.startswith("safety-") and name not in {"safety-foundation", "safety-fixtures"}:
                self.assertIn("--safety", by_id[name].commands[0])
        self.assertEqual(by_id["safety-Add-arm64-advsimd"].commands,
                         (("verification/Runner/Verification.csproj", "verify", "--method", "Add", "--profile", "arm64-advsimd", "--safety"),))
        self.assertEqual(by_id["safety-robustness-Add"].commands,
                         (("verification/Runner.Tests/Verification.Tests.csproj", "robustness", "--method", "Add",
                           "--case", "Renamed", "--case", "ReversedStore", "--safety"),))
        self.assertEqual({name for name in by_id if not any(name.startswith(p) for p in expected_counts)},
                         expected_foundations)
        equality = [name for name, entry in checks.api_entries().items()
                    if entry.get("verification", {}).get("fixtureGroup") == "Equality"]
        self.assertEqual({name for name in by_id if name.startswith("equality-")},
                         {f"equality-{method}-{profile}" for method, profile in checks.coverage_plan(equality)})
        for name, job in by_id.items():
            if name.startswith("equality-"):
                self.assertEqual(job.commands[0][:2], ("verification/Runner.Tests/Verification.Tests.csproj", "equality-fixtures"))
        self.assertEqual({name for name in by_id if name.startswith("multiply-")},
                         {"multiply-" + profile for profile in checks.MULTIPLY_PROFILES})
        for profile in checks.MULTIPLY_PROFILES:
            self.assertEqual(by_id["multiply-" + profile].commands[0],
                ("verification/Runner.Tests/Verification.Tests.csproj", "multiply-fixtures", "--profile", profile, "--workspace"))
        for method in ("Add", "Subtract"):
            for profile in checks.PROFILES[1:]:
                self.assertEqual(by_id[f"simd-{method}-{profile}"].commands[0],
                    ("verification/Runner.Tests/Verification.Tests.csproj", "simd-fixtures", "--method", method, "--profile", profile, "--suite", "all"))
        self.assertEqual({name for name in by_id if name.startswith("simd-")},
                         {f"simd-{method}-{profile}" for method in ("Add", "Subtract")
                          for profile in checks.PROFILES[1:]})
        self.assertEqual({name for name in by_id if name.startswith("reporting-")},
                         {f"reporting-{method}-{profile}" for method in ("AddOverflow", "SubtractUnderflow")
                          for profile in checks.PROFILES})
        for method in ("AddOverflow", "SubtractUnderflow"):
            for profile in checks.PROFILES:
                self.assertEqual(by_id[f"reporting-{method}-{profile}"].commands[0],
                    ("verification/Runner.Tests/Verification.Tests.csproj", "reporting", "--method", method, "--profile", profile))
        operations = ("Compare", "Bitwise", "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot",
                      "Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh")
        self.assertEqual({name for name in by_id if name.startswith("operation-")},
                         {f"operation-{operation}-{profile}" for operation in operations
                          for profile in ("scalar", "x64-vector256")})
        for operation in operations:
            for profile in ("scalar", "x64-vector256"):
                command = by_id[f"operation-{operation}-{profile}"].commands[0]
                if operation in ("Compare", "Bitwise"):
                    self.assertEqual(command, ("verification/Runner.Tests/Verification.Tests.csproj",
                        "compare-fixtures" if operation == "Compare" else "bitwise-fixtures", "--profile", profile, "--workspace"))
                    continue
                if operation in operations[2:6]:
                    self.assertEqual(command, ("verification/Runner.Tests/Verification.Tests.csproj", "bitwise-operator-fixtures",
                        "--method", operation, "--profile", profile, "--workspace"))
                else:
                    self.assertEqual(command, ("verification/Runner.Tests/Verification.Tests.csproj", "shift-fixtures",
                        "--method", operation, "--safety", "--profile", profile, "--workspace"))
        for job in plan:
            for command in job.commands:
                self.assertTrue((checks.ROOT / command[0]).is_file(), command)
            if job.id.startswith(("equality-", "multiply-", "reporting-", "operation-")):
                self.assertNotIn("--case", job.commands[0])

    def test_legacy_baseline_precedes_complete_negative_runner(self):
        for method, negative in (("Add", ("verification/Runner.Tests/Verification.Tests.csproj", "add-negative")), ("Subtract", ("verification/Runner.Tests/Verification.Tests.csproj", "subtract-negative"))):
            job = next(job for job in checks.regression_plan() if job.id == "legacy-" + method)
            self.assertEqual(job.commands, (
                ("verification/Runner/Verification.csproj", "verify", "--method", method, "--profile", "scalar"),
                negative,
            ))

    def test_incomplete_coverage_fails_closed(self):
        original = checks.coverage_plan
        with patch.object(checks, "coverage_plan", side_effect=lambda methods: original(methods)[:-1]):
            with self.assertRaisesRegex(RuntimeError, "Incomplete"):
                checks.regression_plan()

    def test_print_plan_is_read_only_and_exact_job_selection(self):
        with patch.object(checks, "run_suite") as runner, redirect_stdout(io.StringIO()) as output:
            checks.main(["--print-plan", "--job", "legacy-Add"])
        runner.assert_not_called()
        printed = json.loads(output.getvalue())
        self.assertEqual(printed["scope"], "partial")
        self.assertEqual([job["id"] for job in printed["jobs"]], ["legacy-Add"])
        for arguments in (["--job", "legacy"], ["--jobs", "0"], ["--jobs", "9"]):
            with redirect_stdout(io.StringIO()), patch("sys.stderr", io.StringIO()):
                with self.assertRaises(SystemExit):
                    checks.main(arguments)


class ExecutionChecks(unittest.TestCase):
    def setUp(self):
        output = redirect_stdout(io.StringIO())
        output.__enter__()
        self.addCleanup(output.__exit__, None, None, None)
        self.temporary = tempfile.TemporaryDirectory(prefix="int256-all-checks-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.root = self.directory / "root"
        self.root.mkdir()
        (self.root / "source.txt").write_text("immutable", encoding="utf-8")
        self.output = self.directory / "receipts"
        self.expected = {"source.txt": checks.sha(self.root / "source.txt")}
        for target, value in (("ROOT", self.root), ("source_inputs", lambda: self.inputs(self.root)),
                              ("inputs_at", self.inputs), ("clone_source", lambda source, destination: destination.mkdir()),
                              ("run_process", self.success)):
            manager = patch.object(checks, target, value)
            manager.start()
            self.addCleanup(manager.stop)
        manager = patch.object(checks, "copy_source", self.copy_seed)
        manager.start()
        self.addCleanup(manager.stop)

    @staticmethod
    def inputs(directory):
        return {"source.txt": checks.sha(directory / "source.txt")}

    def copy_seed(self, destination):
        shutil.copytree(self.root, destination, dirs_exist_ok=True)

    @staticmethod
    def success(command, directory, log):
        log.write_text("passed\n", encoding="utf-8")
        return 0

    def test_failed_baseline_skips_negative_and_invalidates_full_report(self):
        self.output.mkdir()
        (self.output / "report.json").write_text("old full success", encoding="utf-8")
        job = checks.Job("legacy-Add", (("baseline.py",), ("negative.py",)))
        commands = []
        def fail(command, directory, log):
            commands.append(command)
            log.write_text("failure", encoding="utf-8")
            return 7
        with patch.object(checks, "run_process", fail):
            with self.assertRaisesRegex(RuntimeError, "suite failed"):
                checks.run_suite([job], [job], 1, self.output)
        self.assertEqual(len(commands), 1)
        self.assertTrue(commands[0][1].endswith("baseline.py"))
        self.assertFalse((self.output / "report.json").exists())
        receipt = json.loads(next(self.output.glob("run-*/legacy-Add/receipt.json")).read_text())
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["commands"][0]["exitCode"], 7)
        self.assertEqual(receipt["commands"][0]["logSha256"], checks.sha(
            next(self.output.glob("run-*/legacy-Add/1.log"))))

    def test_csharp_project_uses_dotnet_runner(self):
        job = checks.Job("csharp-runner", (("verification/Runner.Tests/Verification.Tests.csproj",),))
        commands = []
        def capture(command, directory, log):
            commands.append(command)
            return self.success(command, directory, log)
        with patch.object(checks, "run_process", capture):
            checks.run_suite([job], [job], 1, self.output)
        self.assertEqual(len(commands), 1)
        self.assertEqual(commands[0][:3], ["dotnet", "run", "--project"])
        self.assertTrue(commands[0][3].endswith("Verification.Tests.csproj"))
        self.assertEqual(commands[0][4:], ["-c", "Release", "--"])

    def test_immutable_copy_mismatch_prevents_commands_and_aggregate(self):
        job = checks.Job("one", (("runner.py",),))
        def changed_copy(destination):
            self.copy_seed(destination)
            (destination / "source.txt").write_text("changed", encoding="utf-8")
        with patch.object(checks, "copy_source", changed_copy), \
             patch.object(checks, "run_process") as process:
            with self.assertRaisesRegex(RuntimeError, "Immutable source"):
                checks.run_suite([job], [job], 1, self.output)
        process.assert_not_called()
        self.assertFalse((self.output / "report.json").exists())

    def test_source_selector_failure_retains_process_diagnostics_in_receipt(self):
        self.output.mkdir()
        job = checks.Job("selector", (("runner.py",),))
        result = subprocess.CompletedProcess([], 13, "partial output\n", "selector failed: λ\n")
        with patch.object(checks, "inputs_at", INPUTS_AT), \
             patch.object(checks.subprocess, "run", return_value=result) as selector, \
             patch.object(checks, "run_process") as process:
            with self.assertRaisesRegex(RuntimeError, "Source input subprocess failed"):
                checks.run_job(job, self.root, self.expected, self.output)
        process.assert_not_called()
        receipt = json.loads((self.output / "selector/receipt.json").read_text())
        details = json.loads(receipt["error"].split(": ", 1)[1])
        self.assertEqual(details["command"], selector.call_args.args[0])
        self.assertEqual(details["cwd"], receipt["workspace"])
        self.assertEqual(details["exitCode"], 13)
        self.assertEqual(details["stdout"], result.stdout)
        self.assertEqual(details["stderr"], result.stderr)
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["commands"], [])

    def test_job_and_original_source_drift_prevent_success(self):
        job = checks.Job("one", (("runner.py",),))
        for original in (False, True):
            (self.root / "source.txt").write_text("immutable", encoding="utf-8")
            def drift(command, directory, log):
                self.success(command, directory, log)
                ((self.root if original else directory) / "source.txt").write_text("drift", encoding="utf-8")
                return 0
            with patch.object(checks, "run_process", drift):
                with self.assertRaises(RuntimeError):
                    checks.run_suite([job], [job], 1, self.output)
            self.assertFalse((self.output / "report.json").exists())

    def test_bounded_process_overlap_and_distinct_complete_workspaces(self):
        rendezvous = threading.Barrier(2, timeout=10)
        guard = threading.Lock()
        active = maximum = 0
        workspaces = []
        def process(command, directory, log):
            nonlocal active, maximum
            self.assertEqual(self.inputs(directory), self.expected)
            with guard:
                active += 1
                maximum = max(maximum, active)
                workspaces.append(directory)
            rendezvous.wait()
            self.success(command, directory, log)
            with guard:
                active -= 1
            return 0
        plan = [checks.Job(str(index), (("runner.py",),)) for index in range(4)]
        with patch.object(checks, "run_process", process):
            target = checks.run_suite(plan, plan, 2, self.output)
        self.assertEqual(maximum, 2)
        self.assertEqual(len(set(workspaces)), 4)
        report = json.loads(target.read_text())
        self.assertTrue(report["fullSuite"])
        self.assertEqual(len(report["receipts"]), 4)

    def test_partial_success_preserves_full_report_and_labels_subset(self):
        self.output.mkdir()
        full = self.output / "report.json"
        full.write_text("prior full certificate", encoding="utf-8")
        plan = [checks.Job(name, (("runner.py",),)) for name in ("one", "two")]
        target = checks.run_suite(plan, plan[:1], 1, self.output)
        self.assertEqual(full.read_text(), "prior full certificate")
        report = json.loads(target.read_text())
        self.assertEqual(report["scope"], "partial")
        self.assertFalse(report["fullSuite"])
        self.assertEqual(report["selectedJobs"], ["one"])
        self.assertNotEqual(target, full)

    def test_failure_waits_for_running_work_and_writes_no_aggregate(self):
        rendezvous = threading.Barrier(2, timeout=10)
        finished = threading.Event()
        def process(command, directory, log):
            rendezvous.wait()
            log.write_text("runner outcome", encoding="utf-8")
            if command[1].endswith("failure.py"):
                return 1
            finished.set()
            return 0
        plan = [checks.Job(name, ((name + ".py",),)) for name in ("failure", "running")]
        with patch.object(checks, "run_process", process):
            with self.assertRaisesRegex(RuntimeError, "suite failed"):
                checks.run_suite(plan, plan, 2, self.output)
        self.assertTrue(finished.is_set())
        self.assertFalse((self.output / "report.json").exists())
        self.assertEqual(len(list(self.output.glob("run-*/**/receipt.json"))), 2)

    def test_plan_capture_mismatch_prevents_seed_or_command_execution(self):
        job = checks.Job("one", (("runner.py",),))
        with patch.object(checks, "clone_source") as clone, patch.object(checks, "run_process") as process:
            with self.assertRaisesRegex(RuntimeError, "after command-plan selection"):
                checks.run_suite([job], [job], 1, self.output, {"source.txt": "stale"})
        clone.assert_not_called()
        process.assert_not_called()
        self.assertFalse((self.output / "report.json").exists())


if __name__ == "__main__":
    unittest.main()
