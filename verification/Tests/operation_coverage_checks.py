"""Check exact new-API certificates before complete coverage composition."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import coverage_checks
import verify_all
from gate_templates import audit_module
from methods import api_entries, method_manifest


class OperationCoverageChecks(unittest.TestCase):
    def setUp(self):
        coverage_checks.CoverageChecks.setUp(self)
        self.manifest = verify_all.method_manifest("LtUInt256UInt256")
        self.report["scope"] = copy.deepcopy(self.manifest)
        self.report["scope"]["environment"]["selectedProfile"] = "x64-avx2"
        names = verify_all.audit_names("LtUInt256UInt256")
        self.report["auditedTheorems"] = names
        self.report["axiomAudits"] = {name: ["propext", "Quot.sound"] for name in names}
        self.report["coverage"] = {
            "kind": "program-agreement", "aggregateChecked": False,
            "representative": "x64-avx2",
            "condition": "Valid profile agreeing on actual program feature queries and operation availability"}
        artifact = self.report["artifact"]
        convention = self.manifest["callingConvention"]
        artifact["methods"] = [{"signature": self.manifest["entry"],
                                "isStatic": convention["static"],
                                "returnType": convention["returns"],
                                "hasThis": not convention["static"],
                                "parameters": [{"type": p["type"], "IsIn": p["isIn"], "IsOut": p["isOut"]}
                                               for p in convention["parameters"]]}]
        self.write_artifact()
        self.write_report()
        patcher = patch.object(verify_all, "method_manifest", return_value=self.manifest)
        patcher.start()
        self.addCleanup(patcher.stop)

    def write_report(self):
        coverage_checks.CoverageChecks.write_report(self)

    def write_artifact(self):
        (self.directory / "artifact.json").write_text(json.dumps(self.report["artifact"]), encoding="utf-8")

    def check(self):
        return verify_all.checked_certificate("LtUInt256UInt256", "x64-avx2", self.inputs)

    def test_exact_conditional_certificate(self):
        certificate = self.check()
        self.assertEqual(certificate["auditedTheorems"], self.report["auditedTheorems"])
        self.assertNotIn("compositionCertificate", certificate)

    def test_conditional_certificate_cannot_claim_complete_coverage(self):
        self.report["coverage"]["aggregateChecked"] = True
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "conditional program coverage"):
            self.check()

    def test_scope_must_match_selected_contract(self):
        self.report["scope"]["verification"]["contract"] = "different contract"
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "contract scope mismatch"):
            self.check()

    def test_metadata_direction_tampering_even_when_report_and_artifact_match(self):
        self.report["artifact"]["methods"][0]["parameters"][0]["IsIn"] = False
        self.write_artifact()
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "parameter type/direction"):
            self.check()

    def test_stale_extraction_is_rejected(self):
        (self.directory / "Extracted.lean").write_text("-- changed code\n", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "Stale extraction"):
            self.check()

    def test_fixture_cannot_supply_production_certificate(self):
        self.report["source"]["kind"] = "fixture"
        self.write_report()
        with self.assertRaisesRegex(RuntimeError, "production certificate"):
            self.check()

    def test_template_certificate_requires_exact_retained_audit_module(self):
        entry = api_entries()["LtUInt256UInt64"]
        self.manifest.clear()
        self.manifest.update(method_manifest("LtUInt256UInt64"))
        self.report["scope"] = copy.deepcopy(self.manifest)
        self.report["scope"]["environment"]["selectedProfile"] = "x64-avx2"
        names = self.manifest["verification"]["auditedTheorems"]
        self.report["coverage"].update(kind="all-valid-profiles",
            condition="Every valid profile; kernel-checked independence of actual program operations")
        self.report["auditedTheorems"] = names
        self.report["axiomAudits"] = {name: ["propext", "Quot.sound"] for name in names}
        body = self.report["artifact"]["methods"][0]
        body["signature"] = self.manifest["entry"]
        body["parameters"] = [{"type": p["type"], "IsIn": p["isIn"], "IsOut": p["isOut"]}
                              for p in self.manifest["callingConvention"]["parameters"]]
        module = audit_module(entry)
        target = self.directory / "SelectedGate.lean"
        target.write_text(module, encoding="utf-8", newline="\n")
        self.report["generatedGateSha256"] = hashlib.sha256(module.encode("utf-8")).hexdigest()
        self.write_artifact()
        self.write_report()
        with (patch.object(verify_all, "api_entries", return_value={"LtUInt256UInt256": entry}),
              patch.object(verify_all, "audit_names", return_value=names)):
            self.check()
            target.write_text(module + "-- changed audit\n", encoding="utf-8", newline="\n")
            with self.assertRaisesRegex(RuntimeError, "Stale typed audit module"):
                self.check()


if __name__ == "__main__":
    unittest.main()
