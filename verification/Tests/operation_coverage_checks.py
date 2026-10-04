"""Check exact new-API certificates before complete coverage composition."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import threading
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import coverage_checks
import verify_all
from gate_templates import audit_module
from methods import api_entries, method_manifest


class OperationCoverageChecks(unittest.TestCase):
    def test_parallel_profiles_share_build_and_wait_for_each_proof(self):
        bundle = {"assemblySha256": "one fresh production assembly"}
        rendezvous = threading.Barrier(2, timeout=10)
        completed = []

        def proof(arguments, prepared):
            self.assertIs(prepared, bundle)
            rendezvous.wait()
            completed.append(tuple(arguments))

        plan = [("Lsh", "scalar"), ("Lsh", "x64-vector256")]
        with patch.object(verify_all, "verify_one", side_effect=proof):
            verify_all.verify_profiles(plan, bundle, 2)
        self.assertCountEqual(completed, [
            ("--method", method, "--profile", profile) for method, profile in plan])

    def test_parallel_proof_failure_prevents_composition_and_invalidates_report(self):
        aggregate = self.directory / "coverage.json"
        aggregate.write_text('{"status":"verified"}', encoding="utf-8")
        with patch.object(sys, "argv", ["verify_all.py", "--method", "Lsh", "--jobs", "2"]), \
             patch.object(verify_all, "coverage_plan", return_value=[("Lsh", "scalar"), ("Lsh", "x64-vector256")]), \
             patch.object(verify_all, "source_inputs", return_value=self.inputs), \
             patch.object(verify_all, "build_artifact", return_value={"timings": {}}), \
             patch.object(verify_all, "verify_one", side_effect=RuntimeError("kernel rejection")), \
             patch.object(verify_all, "check_composition") as composition:
            with self.assertRaisesRegex(RuntimeError, "kernel rejection"):
                verify_all.main()
        composition.assert_not_called()
        self.assertFalse(aggregate.exists())

    def test_parallel_jobs_rejects_nonpositive_count(self):
        for count in ("0", "-1"):
            with self.subTest(count=count), patch.object(sys, "argv", ["verify_all.py", "--jobs", count]), \
                 patch.object(sys, "stderr"):
                with self.assertRaises(SystemExit):
                    verify_all.main()

    def test_duplicate_profile_flags_cannot_satisfy_total_family_premises(self):
        original = verify_all.expected_profile
        for method, profile, key in (("Lsh", "x64-vector256", "Vector256Accelerated"),
                                     ("EqUInt256UInt256", "x64-sse41", "Sse41"),
                                     ("LtUInt256UInt256", "x64-vector256", "Vector256Accelerated"),
                                     ("Multiply", "arm64-armbase-vector256", "ArmBase64")):
            manifest = method_manifest(method)
            def changed(name):
                values = original(name)
                if name == profile:
                    values[key] = False
                return values
            with self.subTest(method=method), \
                 patch.object(verify_all, "method_manifest", return_value=manifest), \
                 patch.object(verify_all, "expected_profile", side_effect=changed):
                with self.assertRaisesRegex(RuntimeError, "representative premise changed"):
                    verify_all.coverage_plan([method])

    def test_multiply_representatives_cover_independent_storage_and_arithmetic(self):
        manifest = method_manifest("Multiply")
        representatives = manifest["verification"]["familyCoverage"]["representatives"]
        arithmetic = {(False, False, False, False), (False, False, False, True),
                      (False, False, True, True), (True, False, False, False),
                      (True, False, False, True), (True, False, True, True),
                      (False, True, False, False)}
        observed = set()
        for name in representatives:
            profile = verify_all.expected_profile(name)
            observed.add(tuple(profile[key] for key in
                ("Bmi2", "ArmBase64", "Avx512DQVL", "Avx2", "Vector256Accelerated")))
        self.assertEqual(observed, {flags + (storage,) for flags in arithmetic for storage in (False, True)})
        self.assertEqual(len(representatives), len(observed))
        with patch.object(verify_all, "method_manifest", return_value=manifest):
            self.assertEqual(verify_all.coverage_plan(["Multiply"]),
                             [("Multiply", name) for name in representatives])

    def setUp(self):
        coverage_checks.CoverageChecks.setUp(self)
        self.manifest = verify_all.method_manifest("LtUInt256UInt256")
        self.report["scope"] = copy.deepcopy(self.manifest)
        self.report["scope"]["environment"]["selectedProfile"] = "x64-avx2"
        names = verify_all.audit_names("LtUInt256UInt256")
        self.report["auditedTheorems"] = names
        self.report["axiomAudits"] = {name: ["propext", "Quot.sound"] for name in names}
        module = audit_module(api_entries()["LtUInt256UInt256"])
        (self.directory / "SelectedGate.lean").write_text(module, encoding="utf-8", newline="\n")
        self.report["generatedGateSha256"] = hashlib.sha256(module.encode("utf-8")).hexdigest()
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

    def test_total_plan_requires_more_than_a_conditional_gate(self):
        self.manifest["verification"].pop("familyCoverage", None)
        with self.assertRaisesRegex(RuntimeError, "Total feature coverage"):
            verify_all.coverage_plan(["LtUInt256UInt256"])

    def test_total_plan_selects_a_universal_gate_once(self):
        manifest = method_manifest("LtUInt256UInt64")
        with patch.object(verify_all, "method_manifest", return_value=manifest):
            self.assertEqual(verify_all.coverage_plan(["LtUInt256UInt64"]), [("LtUInt256UInt64", "scalar")])

    def test_total_plan_requires_both_storage_feature_values(self):
        manifest = method_manifest("Lsh")
        with patch.object(verify_all, "method_manifest", return_value=manifest):
            self.assertEqual(verify_all.coverage_plan(["Lsh"]), [("Lsh", "scalar"), ("Lsh", "x64-vector256")])

    def test_reduction_plan_keeps_the_sse41_fallback_representative(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["verification"]["familyCoverage"] = {
            "kind": "vector-reduction", "theorem": "checked_family",
            "representatives": ["scalar", "x64-sse41", "x64-vector256"]}
        with patch.object(verify_all, "method_manifest", return_value=manifest):
            self.assertEqual(verify_all.coverage_plan(["EqUInt256UInt256"]),
                [("EqUInt256UInt256", profile) for profile in ("scalar", "x64-sse41", "x64-vector256")])

    def test_relational_plan_keeps_each_dispatch_path(self):
        manifest = copy.deepcopy(self.manifest)
        representatives = ["scalar", "x64-vector256", "x64-avx2", "x64-avx512"]
        manifest["verification"]["familyCoverage"] = {
            "kind": "relational-dispatch", "theorem": "checked_family",
            "representatives": representatives}
        with patch.object(verify_all, "method_manifest", return_value=manifest):
            self.assertEqual(verify_all.coverage_plan(["LtUInt256UInt256"]),
                [("LtUInt256UInt256", profile) for profile in representatives])

    def test_total_plan_rejects_missing_and_duplicate_selection(self):
        for methods in ([], ["Add", "Add"]):
            with self.subTest(methods=methods), self.assertRaisesRegex(RuntimeError, "distinct selected"):
                verify_all.coverage_plan(methods)

    def test_conditional_cli_invalidates_prior_total_report_before_build(self):
        self.manifest["verification"].pop("familyCoverage", None)
        aggregate = self.directory / "coverage.json"
        aggregate.write_text('{"status":"verified"}', encoding="utf-8")
        with patch.object(sys, "argv", ["verify_all.py", "--method", "LtUInt256UInt256"]), \
             patch.object(verify_all, "build_artifact") as build:
            with self.assertRaisesRegex(RuntimeError, "Total feature coverage"):
                verify_all.main()
        build.assert_not_called()
        self.assertFalse(aggregate.exists())

    def test_print_plan_is_read_only_and_never_builds(self):
        aggregate = self.directory / "coverage.json"
        aggregate.write_text("existing certificate", encoding="utf-8")
        manifest = method_manifest("Lsh")
        with patch.object(sys, "argv", ["verify_all.py", "--method", "Lsh", "--print-plan"]), \
             patch.object(verify_all, "method_manifest", return_value=manifest), \
             patch.object(verify_all, "print", create=True) as output, \
             patch.object(verify_all, "build_artifact") as build:
            verify_all.main()
        build.assert_not_called()
        output.assert_called_once()
        self.assertEqual(json.loads(output.call_args.args[0]), {"include": [
            {"method": "Lsh", "profile": "scalar"}, {"method": "Lsh", "profile": "x64-vector256"}]})
        self.assertEqual(aggregate.read_text(encoding="utf-8"), "existing certificate")

    def test_incomplete_print_plan_cannot_emit_a_partial_matrix(self):
        self.manifest["verification"].pop("familyCoverage", None)
        with patch.object(sys, "argv", ["verify_all.py", "--method", "LtUInt256UInt256", "--print-plan"]), \
             patch.object(verify_all, "print", create=True) as output, \
             patch.object(verify_all, "build_artifact") as build:
            with self.assertRaisesRegex(RuntimeError, "Total feature coverage"):
                verify_all.main()
        output.assert_not_called()
        build.assert_not_called()

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

    def test_handwritten_certificate_requires_its_retained_typed_binding(self):
        target = self.directory / "SelectedGate.lean"
        target.write_text("-- missing contract binding\n", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "Stale typed audit module"):
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
