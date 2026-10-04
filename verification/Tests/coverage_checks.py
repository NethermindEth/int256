"""Reject incomplete, stale or mismatched aggregate family certificates."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verify_all
from common import VERIFY, sha
from verify import theorem_audits


class CoverageChecks(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.verify = self.root / "verification"
        self.directory = self.verify / "generated/profiles/x64-avx2/add"
        self.directory.mkdir(parents=True)
        (self.verify / "manifests").mkdir()
        manifest = json.loads((VERIFY / "manifests/add.json").read_text(encoding="utf-8"))
        (self.verify / "manifests/add.json").write_text(json.dumps(manifest), encoding="utf-8")
        (self.verify / "manifests/subtract.json").write_bytes((VERIFY / "manifests/subtract.json").read_bytes())
        for name in ("lakefile.toml", "lean-toolchain"):
            (self.verify / name).write_bytes((VERIFY / name).read_bytes())
        proof = self.verify / "Gate.lean"
        proof.write_text("-- independent test proof input\n", encoding="utf-8")
        (self.directory / "Extracted.lean").write_text("-- independent test extraction\n", encoding="utf-8")
        artifact = {"profile": verify_all.expected_profile("x64-avx2"), "entryIndex": 0,
                    "methods": [{"signature": manifest["entry"]}], "sha256": "assembly",
                    "staticData": [{"bytes": "00010203"}]}
        (self.directory / "artifact.json").write_text(json.dumps(artifact), encoding="utf-8")
        names = verify_all.audit_names("Add")
        self.inputs = {"verification/Gate.lean": sha(proof)}
        self.inputs.update({f"verification/{name}": sha(self.verify / name)
                            for name in ("lakefile.toml", "lean-toolchain")})
        self.report = {"status": "verified", "source": {
                           "kind": "production", "project": "src/Nethermind.Int256/Nethermind.Int256.csproj",
                           "fixture": None},
                       "semanticsVersion": verify_all.SEMANTICS_VERSION,
                       "sourceInputs": self.inputs, "leanSourceSha256": {"Gate.lean": sha(proof)},
                       "artifact": artifact, "generatedProgramSha256": sha(self.directory / "Extracted.lean"),
                       "executionProfile": artifact["profile"], "auditedTheorems": names,
                       "axiomAudits": {name: ["propext", "Quot.sound"] for name in names},
                       "coverage": {"kind": "feature-family", "representative": "x64-avx2"}}
        self.write_report()
        for name, value in (("ROOT", self.root), ("VERIFY", self.verify),
                            ("generated_directory", lambda *args: self.directory)):
            patcher = patch.object(verify_all, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def write_report(self):
        (self.directory / "report.json").write_text(json.dumps(self.report), encoding="utf-8")

    def check(self):
        return verify_all.checked_certificate("Add", "x64-avx2", self.inputs)

    def test_valid_family_certificate(self):
        self.assertEqual(self.check()["familyTheorem"], "UInt256Proof.checked_contract_family")

    def test_missing_family_gate(self):
        self.report["auditedTheorems"].pop()
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "Missing family gate"):
            self.check()

    def test_fixture_cannot_supply_production_coverage(self):
        self.report["source"]["kind"] = "fixture"
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "production certificate"):
            self.check()

    def test_relabelled_fixture_project(self):
        self.report["source"]["project"] = "verification/Tests/Fixtures/SIMD/Nethermind.Int256.csproj"
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "production certificate"):
            self.check()

    def test_relabelled_fixture_source(self):
        self.report["source"]["fixture"] = "verification/Tests/Fixtures/SIMD/Renamed.cs"
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "production certificate"):
            self.check()

    def test_missing_production_provenance(self):
        self.report["source"] = {"kind": "production"}
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "production certificate"):
            self.check()

    def test_changed_proof_inputs(self):
        (self.verify / "Gate.lean").write_text("-- changed semantics\n", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "Stale proof inputs"):
            self.check()

    def test_changed_generated_program(self):
        (self.directory / "Extracted.lean").write_text("-- changed lane order\n", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "Stale extraction"):
            self.check()

    def assert_composition_mutation_rejected(self, mutate):
        aggregate = self.verify / "generated/coverage.json"
        aggregate.write_text('{"status":"verified"}', encoding="utf-8")

        def composition(inputs, operations=False):
            mutate()
            return {}

        with patch.object(verify_all, "METHODS", ("Add",)), \
             patch.object(verify_all, "PROFILES", ("x64-avx2",)), \
             patch.object(verify_all, "source_inputs", return_value=self.inputs), \
             patch.object(verify_all, "check_composition", side_effect=composition), \
             patch.object(sys, "argv", ["verify_all.py", "--check-reports"]):
            with self.assertRaisesRegex(RuntimeError, "Stale extraction"):
                verify_all.main()
        self.assertFalse(aggregate.exists())

    def test_table_changed_during_composition(self):
        def mutate():
            artifact = copy.deepcopy(self.report["artifact"])
            artifact["staticData"][0]["bytes"] = "00010204"
            (self.directory / "artifact.json").write_text(json.dumps(artifact), encoding="utf-8")
        self.assert_composition_mutation_rejected(mutate)

    def test_program_changed_during_composition(self):
        self.assert_composition_mutation_rejected(lambda:
            (self.directory / "Extracted.lean").write_text("-- changed during checking\n", encoding="utf-8"))

    def test_transient_edit_during_composition_copy(self):
        original_copy = verify_all.shutil.copy2

        def transient_copy(source, target, *args, **kwargs):
            source = Path(source)
            if source.name != "Gate.lean":
                return original_copy(source, target, *args, **kwargs)
            captured = source.read_bytes()
            try:
                source.write_text("-- different composition proof\n", encoding="utf-8")
                return original_copy(source, target, *args, **kwargs)
            finally:
                source.write_bytes(captured)

        with patch.object(verify_all.shutil, "which", return_value="lake"), \
             patch.object(verify_all.shutil, "copy2", side_effect=transient_copy), \
             patch.object(verify_all, "source_inputs", return_value=self.inputs), \
             patch.object(verify_all, "run", return_value="Lean (version 4.34.1)") as kernel:
            with self.assertRaisesRegex(RuntimeError, "Proof snapshot"):
                verify_all.check_composition(self.inputs)
            kernel.assert_called_once_with(["lake", "env", "lean", "--version"], self.verify)

    def test_composition_rejects_unpinned_kernel(self):
        with patch.object(verify_all.shutil, "which", return_value="lake"), \
             patch.object(verify_all, "run", return_value="Lean (version 4.35.0)") as kernel:
            with self.assertRaisesRegex(RuntimeError, "Unexpected composition Lean toolchain"):
                verify_all.check_composition(self.inputs)
            kernel.assert_called_once_with(["lake", "env", "lean", "--version"], self.verify)

    def test_changed_semantics_version(self):
        self.report["semanticsVersion"] = "old-model"
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "Semantics version mismatch"):
            self.check()

    def test_changed_table_bytes(self):
        artifact = copy.deepcopy(self.report["artifact"])
        artifact["staticData"][0]["bytes"] = "00010204"
        (self.directory / "artifact.json").write_text(json.dumps(artifact), encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "Stale extraction"):
            self.check()

    def test_named_profile_with_different_flags(self):
        self.report["executionProfile"] = dict(self.report["executionProfile"], Bmi1=True)
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "Profile mismatch"):
            self.check()

    def test_unapproved_family_axiom(self):
        self.report["axiomAudits"]["UInt256Proof.checked_contract_family"] = ["invented.correctness"]
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "Unapproved family axioms"):
            self.check()

    def test_unclassified_profile(self):
        with self.assertRaisesRegex(RuntimeError, "Unclassified"):
            verify_all.expected_profile("x64-new-isa")

    def test_all_seven_distinct_representatives(self):
        profiles = [verify_all.expected_profile(name) for name in verify_all.PROFILES]
        self.assertEqual(len(profiles), 7)
        self.assertEqual(len({json.dumps(p, sort_keys=True) for p in profiles}), 7)

    def test_public_audit_requires_family(self):
        with self.assertRaisesRegex(RuntimeError, "Missing"):
            theorem_audits("'selected' depends on axioms: []", ["selected", "family"], [])

    def test_kernel_empty_axiom_printout(self):
        self.assertEqual(theorem_audits("'coverage' does not depend on any axioms", ["coverage"], []),
                         {"coverage": []})

    def test_public_audit_rejects_duplicate(self):
        with self.assertRaisesRegex(RuntimeError, "ambiguous"):
            theorem_audits("'family' depends on axioms: []\n'family' depends on axioms: []", ["family"], [])


if __name__ == "__main__":
    unittest.main()
