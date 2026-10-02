"""Reject stale shared build bundles before and after per-profile proof checking."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verify
from common import VERIFY, expected_profile, sha


class PreparedBuildChecks(unittest.TestCase):
    def setUp(self):
        work = tempfile.TemporaryDirectory()
        self.addCleanup(work.cleanup)
        self.root = Path(work.name)
        self.verification = self.root / "verification"
        self.directory = self.verification / "generated"
        self.directory.mkdir(parents=True)
        (self.verification / "manifests").mkdir()
        for name in ("lakefile.toml", "lean-toolchain"):
            (self.verification / name).write_bytes((VERIFY / name).read_bytes())
        self.manifest = json.loads((VERIFY / "manifests/add.json").read_text(encoding="utf-8"))
        (self.verification / "manifests/add.json").write_text(json.dumps(self.manifest), encoding="utf-8")
        self.inputs = {"src/input.cs": "source-hash"}
        (self.verification / "Gate.lean").write_text("-- captured proof source\n", encoding="utf-8")
        self.inputs.update({f"verification/{name}": sha(self.verification / name)
                            for name in ("Gate.lean", "lakefile.toml", "lean-toolchain")})
        self.assembly = self.root / "assembly.dll"
        self.extractor = self.root / "extractor.dll"
        self.assembly.write_bytes(b"versioned test assembly")
        self.extractor.write_bytes(b"versioned test extractor")
        self.bundle = {"sourceInputs": copy.deepcopy(self.inputs), "assembly": self.assembly,
                       "extractor": self.extractor, "assemblySha256": sha(self.assembly),
                       "extractorSha256": sha(self.extractor), "timings": {}, "fixture": None,
                       "project": (self.root / "src/Nethermind.Int256/Nethermind.Int256.csproj").resolve()}
        for name, value in (("ROOT", self.root), ("VERIFY", self.verification),
                            ("generated_directory", lambda *args: self.directory),
                            ("source_inputs", lambda: copy.deepcopy(self.inputs))):
            patcher = patch.object(verify, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def test_valid_bundle(self):
        verify.validate_bundle(self.bundle, self.inputs, production=True)

    def test_changed_source_after_build(self):
        self.inputs["src/input.cs"] = "changed"
        with self.assertRaisesRegex(RuntimeError, "stale source"):
            verify.validate_bundle(self.bundle, self.inputs)

    def test_changed_source_during_validation(self):
        with patch.object(verify, "source_inputs", return_value={"new": "input"}):
            with self.assertRaisesRegex(RuntimeError, "stale source"):
                verify.validate_bundle(self.bundle, self.inputs)

    def test_changed_dll(self):
        self.assembly.write_bytes(b"changed DLL")
        with self.assertRaisesRegex(RuntimeError, "identity changed"):
            verify.validate_bundle(self.bundle, self.inputs)

    def test_changed_extractor(self):
        self.extractor.write_bytes(b"changed extractor")
        with self.assertRaisesRegex(RuntimeError, "identity changed"):
            verify.validate_bundle(self.bundle, self.inputs)

    def test_fixture_bundle_rejected_as_production(self):
        self.bundle["fixture"] = "Baseline"
        with self.assertRaisesRegex(RuntimeError, "cannot verify fixtures"):
            verify.validate_bundle(self.bundle, self.inputs, production=True)

    def test_different_project_rejected_as_production(self):
        self.bundle["project"] = self.root / "different.csproj"
        with self.assertRaisesRegex(RuntimeError, "cannot verify fixtures"):
            verify.validate_bundle(self.bundle, self.inputs, production=True)

    def tool(self, command, cwd):
        if command == ["dotnet", "--version"]:
            return self.manifest["sdk"]
        if command == ["lake", "env", "lean", "--version"]:
            return "Lean (version 4.34.1)"
        if command[:2] == ["dotnet", str(self.extractor)]:
            generated = Path(command[3])
            generated.mkdir(parents=True)
            (generated / "Extracted.lean").write_text("-- test extraction\n", encoding="utf-8")
            artifact = {"sha256": sha(self.assembly), "entryIndex": 0,
                        "methods": [{"signature": self.manifest["entry"]}], "profile": expected_profile("scalar")}
            (generated / "artifact.json").write_text(json.dumps(artifact), encoding="utf-8")
            return ""
        raise AssertionError(f"Unexpected tool call: {command}")

    def seed_reports(self):
        (self.directory / "report.json").write_text("old success", encoding="utf-8")
        (self.directory / "coverage.json").write_text("old coverage", encoding="utf-8")

    def assert_invalidated(self):
        self.assertFalse((self.directory / "report.json").exists())
        self.assertFalse((self.directory / "coverage.json").exists())

    def test_stale_prepared_attempt_invalidates_reports_before_extraction(self):
        self.seed_reports()
        self.bundle["sourceInputs"] = {"old": "source"}
        with patch.object(verify.shutil, "which", return_value="lake"), patch.object(verify, "run", side_effect=self.tool):
            with self.assertRaisesRegex(RuntimeError, "stale source"):
                verify.main([], prepared=self.bundle)
        self.assert_invalidated()

    def test_identity_rechecked_after_kernel_before_report(self):
        self.seed_reports()

        def proof(*args):
            self.extractor.write_bytes(b"changed while proof was running")
            return "\n".join(f"'{name}' depends on axioms: []" for name in verify.audit_names("Add"))

        with patch.object(verify.shutil, "which", return_value="lake"), \
                patch.object(verify, "run", side_effect=self.tool), patch.object(verify, "run_stage", side_effect=proof):
            with self.assertRaisesRegex(RuntimeError, "identity changed"):
                verify.main([], prepared=self.bundle)
        self.assert_invalidated()

    def test_selected_profile_flags_checked_before_kernel(self):
        self.seed_reports()

        def tool(command, cwd):
            result = self.tool(command, cwd)
            if command[:2] == ["dotnet", str(self.extractor)]:
                path = Path(command[3]) / "artifact.json"
                artifact = json.loads(path.read_text(encoding="utf-8"))
                artifact["profile"]["Bmi1"] = True
                path.write_text(json.dumps(artifact), encoding="utf-8")
            return result

        with patch.object(verify.shutil, "which", return_value="lake"), \
                patch.object(verify, "run", side_effect=tool), patch.object(verify, "run_stage") as proof:
            with self.assertRaisesRegex(RuntimeError, "feature profile does not match"):
                verify.main([], prepared=self.bundle)
            proof.assert_not_called()
        self.assert_invalidated()

    def test_transient_edit_during_proof_copy(self):
        self.seed_reports()
        original_copy = verify.shutil.copy2

        def transient_copy(source, target, *args, **kwargs):
            source = Path(source)
            if source.name != "Gate.lean":
                return original_copy(source, target, *args, **kwargs)
            captured = source.read_bytes()
            try:
                source.write_text("-- different proof copied transiently\n", encoding="utf-8")
                return original_copy(source, target, *args, **kwargs)
            finally:
                source.write_bytes(captured)

        with patch.object(verify.shutil, "which", return_value="lake"), \
             patch.object(verify.shutil, "copy2", side_effect=transient_copy), \
             patch.object(verify, "run", side_effect=self.tool), patch.object(verify, "run_stage") as proof:
            with self.assertRaisesRegex(RuntimeError, "Proof snapshot"):
                verify.main([], prepared=self.bundle)
            proof.assert_not_called()
        self.assert_invalidated()


if __name__ == "__main__":
    unittest.main()
