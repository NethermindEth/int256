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

    def decision(self, before, after):
        sdk = '10.0.401'
        with patch.object(changes, "run", side_effect=["src/UInt256.cs\0", sdk, "", "", ""]), \
                patch.object(changes, "extract", side_effect=[before, after]):
            return changes.needs_proof("base")[0]

    def test_unchanged_extraction_skips_proof(self):
        self.assertFalse(self.decision(({"layout": 32}, b"program"), ({"layout": 32}, b"program")))

    def test_changed_program_or_metadata_requires_proof(self):
        self.assertTrue(self.decision(({}, b"before"), ({}, b"after")))
        self.assertTrue(self.decision(({"layout": 32}, b"same"), ({"layout": 64}, b"same")))

    def test_extraction_failure_is_not_a_skip(self):
        with self.assertRaises(RuntimeError):
            self.decision(RuntimeError("unsupported reachable instruction"), ({}, b"program"))

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
