"""Check that method-change selection skips only unchanged verified inputs."""

import copy
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import changes


class ChangeChecks(unittest.TestCase):
    def test_build_and_verification_changes_force_proof(self):
        for path in ("verification/CIL/Execution.lean", "verification/Extractor/Program.cs",
                     "verification/changes.py", "src/Directory.Build.props", "global.json",
                     ".github/workflows/verify-uint256-tests.yml"):
            with self.subTest(path=path):
                self.assertTrue(changes.proof_inputs_changed(["src/UInt256.cs", path]))

    def test_ordinary_csharp_changes_are_compared(self):
        self.assertFalse(changes.proof_inputs_changed(["src/UInt256.cs", "src/Helper.cs"]))

    def test_renaming_a_verification_file_into_source_forces_proof(self):
        with patch.object(changes, "run", return_value="verification/Helper.cs\0src/Helper.cs\0") as run:
            self.assertTrue(changes.needs_proof("base")[0])
        self.assertIn("--no-renames", run.call_args.args[0])

    def test_comparison_preserves_semantic_metadata(self):
        baseline = {"sha256": "old", "assembly": "version1", "layout": {"ClassSize": 32},
                    "methods": [{"token": 1, "signature": "Add", "instructions": ["add"]},
                                {"token": 2, "signature": "Helper", "instructions": ["add"]}]}
        identities = copy.deepcopy(baseline)
        identities.update(sha256="new", assembly="version2")
        identities["methods"][0]["token"] = 100
        self.assertEqual(changes.comparison_artifact(baseline), changes.comparison_artifact(identities))
        for mutate in (lambda value: value["layout"].update(ClassSize=64),
                       lambda value: value["methods"][1].update(instructions=["sub"]),
                       lambda value: value["methods"].append({"signature": "NewHelper"})):
            changed = copy.deepcopy(baseline)
            mutate(changed)
            self.assertNotEqual(changes.comparison_artifact(baseline), changes.comparison_artifact(changed))
        self.assertIn("token", baseline["methods"][0])

    def decision(self, before, after, profile="scalar"):
        sdk = '10.0.401'
        with patch.object(changes, "run", side_effect=["src/UInt256.cs\0", sdk, "", "", ""]), \
                patch.object(changes, "extract", side_effect=[before, after]):
            return changes.needs_proof("base", profile=profile)[0]

    def test_unchanged_extraction_skips_proof(self):
        self.assertFalse(self.decision(({"layout": 32}, b"program"), ({"layout": 32}, b"program")))

    def test_changed_program_or_metadata_requires_proof(self):
        self.assertTrue(self.decision(({}, b"before"), ({}, b"after")))
        self.assertTrue(self.decision(({"layout": 32}, b"same"), ({"layout": 64}, b"same")))

    def test_extraction_failure_is_not_a_skip(self):
        with self.assertRaises(RuntimeError):
            self.decision(RuntimeError("unsupported reachable instruction"), ({}, b"program"))

    def test_subtraction_uses_its_own_dependency_graph(self):
        with patch.object(changes, "run", side_effect=["src/UInt256.cs\0", '10.0.401', "", "", ""]), \
                patch.object(changes, "extract", side_effect=[({}, b"same"), ({}, b"same")]) as extract:
            self.assertFalse(changes.needs_proof("base", "Subtract")[0])
        self.assertTrue(all(call.args[-2:] == ("Subtract", "scalar") for call in extract.call_args_list))

    def test_unknown_method_fails_before_skipping(self):
        with self.assertRaises(ValueError):
            changes.needs_proof("", "Unknown")

    def test_unknown_profile_fails_before_skipping(self):
        with self.assertRaises(ValueError):
            changes.needs_proof("", profile="unknown")

    def test_each_profile_uses_its_selected_dependency_graph(self):
        for profile in changes.PROFILES:
            with self.subTest(profile=profile), \
                    patch.object(changes, "run", side_effect=["src/UInt256.cs\0", '10.0.401', "", "", ""]), \
                    patch.object(changes, "extract", side_effect=[({}, b"same"), ({}, b"same")]) as extract:
                self.assertFalse(changes.needs_proof("base", "Subtract", profile)[0])
                self.assertTrue(all(call.args[-2:] == ("Subtract", profile) for call in extract.call_args_list))

    def test_profile_static_data_and_intrinsic_metadata_are_compared(self):
        baseline = {"sha256": "old", "assembly": "version1", "profile": {"Name": "x64-avx2", "Bmi1": False},
                    "queriedFeatures": ["Avx2"], "staticData": [{"bytes": "0100", "size": 2, "packing": 1}],
                    "methods": [{"token": 1, "signature": "Add", "instructions": [
                        {"opcode": "call", "operand": "Avx2::Permute4x64", "scope": "System.Runtime.Intrinsics"},
                        {"opcode": "ldc.i4", "operand": "144"}]}]}
        mutations = (
            lambda value: value["profile"].update(Name="x64-avx512"),
            lambda value: value["profile"].update(Bmi1=True),
            lambda value: value["queriedFeatures"].append("Bmi1"),
            lambda value: value["staticData"][0].update(bytes="0000"),
            lambda value: value["staticData"][0].update(packing=8),
            lambda value: value["methods"][0]["instructions"][0].update(operand="Avx2::Blend"),
            lambda value: value["methods"][0]["instructions"][0].update(scope="Other.Assembly"),
            lambda value: value["methods"][0]["instructions"][1].update(operand="145"),
        )
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                changed = copy.deepcopy(baseline)
                mutate(changed)
                self.assertNotEqual(changes.comparison_artifact(baseline), changes.comparison_artifact(changed))

    def test_extraction_profile_mismatch_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            generated = work / "generated"
            generated.mkdir()
            (generated / "artifact.json").write_text('{"profile":{"Name":"scalar"}}', encoding="utf-8")
            with patch.object(changes, "run"), self.assertRaisesRegex(RuntimeError, "profile mismatch"):
                changes.extract(changes.ROOT, work, Path("extractor.dll"), "Add", "x64-avx2")

    def test_extraction_method_mismatch_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            generated = work / "generated"
            generated.mkdir()
            (generated / "artifact.json").write_text(
                '{"profile":{"Name":"scalar"},"entryIndex":0,"methods":[{"signature":"Other"}]}',
                encoding="utf-8")
            with patch.object(changes, "run"), self.assertRaisesRegex(RuntimeError, "method mismatch"):
                changes.extract(changes.ROOT, work, Path("extractor.dll"))

    def test_profile_model_and_aggregate_inputs_force_proof(self):
        for path in ("verification/CIL/Features.lean", "verification/CIL/ProfileEquivalence.lean",
                     "verification/Extractor/StaticData.cs", "verification/AggregateAudit.lean"):
            with self.subTest(path=path):
                self.assertTrue(changes.proof_inputs_changed([path]))

    def test_cli_passes_selected_profile_to_change_detection(self):
        with patch.object(sys, "argv", ["changes.py", "--method", "Subtract", "--profile", "x64-avx512-bmi1"]), \
                patch.dict(os.environ, {"VERIFY_EVENT": "push", "VERIFY_BASE": "base", "GITHUB_OUTPUT": "",
                                        "GITHUB_STEP_SUMMARY": ""}), \
                patch.object(changes, "needs_proof", return_value=(True, "Selected profile")) as detect:
            changes.main()
        detect.assert_called_once_with("base", "Subtract", "x64-avx512-bmi1")

    def test_cli_rejects_unknown_profile_even_for_manual_dispatch(self):
        with patch.object(sys, "argv", ["changes.py", "--profile", "unknown"]), \
                patch.dict(os.environ, {"VERIFY_EVENT": "workflow_dispatch"}), \
                patch.object(changes, "needs_proof") as detect, self.assertRaises(SystemExit):
            changes.main()
        detect.assert_not_called()

    def test_missing_base_requires_proof(self):
        self.assertTrue(changes.needs_proof("")[0])
        self.assertTrue(changes.needs_proof("0" * 40)[0])

    def test_manual_dispatch_always_requires_proof(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "output"
            with patch.dict(os.environ, {"VERIFY_EVENT": "workflow_dispatch", "GITHUB_OUTPUT": str(output),
                                         "GITHUB_STEP_SUMMARY": ""}), patch.object(changes, "needs_proof") as detect:
                changes.main()
            detect.assert_not_called()
            self.assertEqual(output.read_text().strip(), "required=true")

    def test_pr_into_unverified_branch_requires_proof(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "output"
            with patch.dict(os.environ, {"VERIFY_EVENT": "pull_request", "VERIFY_BASE_BRANCH": "feature",
                                         "GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": ""}), \
                    patch.object(changes, "needs_proof") as detect:
                changes.main()
            detect.assert_not_called()
            self.assertEqual(output.read_text().strip(), "required=true")


if __name__ == "__main__":
    unittest.main()
