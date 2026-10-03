"""Checks for exact API selection, metadata matching and fail-closed reporting."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import common
import methods
import verify


class MethodChecks(unittest.TestCase):
    def test_refutation_templates_are_freshness_inputs(self):
        inputs = verify.source_inputs()
        for relative in ("Compare/RefutationTemplate.lean.in", "Bitwise/RefutationTemplate.lean.in",
                         "Shift/RefutationTemplate.lean.in", "Shift/OperatorRefutationTemplate.lean.in"):
            path = common.VERIFY / "Tests/Fixtures" / relative
            self.assertEqual(inputs[path.relative_to(common.ROOT).as_posix()], common.sha(path))

    def test_axiom_audits_accept_lean_line_wrapping(self):
        name = "UInt256Proof.Compare.checked_three_way_all_profiles_contract"
        approved = ["propext", "Classical.choice", "Quot.sound"]
        output = f"info: Audit.lean:1:0: '{name}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
        self.assertEqual(verify.theorem_audits(output, [name], approved), {name: approved})
        self.assertEqual(verify.theorem_audits(
            f"'{name}' does not depend on any axioms", [name], approved), {name: []})

    def test_wrapped_audit_still_rejects_unapproved_and_duplicate_axioms(self):
        for axioms in ("propext,\n sorryAx", "propext,\n propext"):
            with self.subTest(axioms=axioms), self.assertRaisesRegex(RuntimeError, "Unapproved or duplicate"):
                verify.theorem_audits(f"'Gate' depends on axioms: [{axioms}]", ["Gate"], ["propext"])

    def test_audit_cannot_cross_a_diagnostic_or_accept_duplicates(self):
        for output in ("'Gate' depends on axioms: [propext,\nerror: missing close\n]",
                       "'Gate' depends on axioms: [propext]\n'Gate' depends on axioms: [propext]"):
            with self.subTest(output=output), self.assertRaisesRegex(RuntimeError, "Missing or ambiguous"):
                verify.theorem_audits(output, ["Gate"], ["propext"])

    def test_metadata_directions_and_receiver_are_contract_inputs(self):
        expected = methods.api_entries()["LtUInt256UInt256"]["callingConvention"]
        actual = {"isStatic": expected["static"], "returnType": expected["returns"],
                  "hasThis": not expected["static"], "parameters": [
                      {"Name": "renamed", "type": item["type"],
                       "IsIn": item["isIn"], "IsOut": item["isOut"]}
                      for item in expected["parameters"]]}
        methods.check_calling_convention(actual, expected)
        mutations = [("isStatic", False), ("returnType", "System.Void"), ("hasThis", True)]
        for key, value in mutations:
            changed = copy.deepcopy(actual)
            changed[key] = value
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                methods.check_calling_convention(changed, expected)
        for key, value in (("type", "System.UInt64"), ("IsIn", False), ("IsOut", True)):
            changed = copy.deepcopy(actual)
            changed["parameters"][0][key] = value
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                methods.check_calling_convention(changed, expected)

    def test_missing_proof_invalidates_prior_success_before_failing(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = directory / "generated/operations/AddOverflow/scalar/report.json"
            report.parent.mkdir(parents=True)
            report.write_text(json.dumps({"status": "verified"}), encoding="utf-8")
            pending = copy.deepcopy(methods.api_entries()["AddOverflow"])
            pending.pop("verification", None)
            with (patch.object(common, "VERIFY", directory), patch.object(verify, "VERIFY", directory),
                  patch.object(methods, "api_entries", return_value={"AddOverflow": pending})):
                with self.assertRaisesRegex(RuntimeError, "proof is not implemented"):
                    verify.main(["--method", "AddOverflow"])
            self.assertFalse(report.exists())

    def test_unknown_selector_cannot_escape_generated_directory(self):
        for selector in ("../Add", "Unknown", "System.Void::Add"):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                common.generated_directory(selector)

    def test_distinct_entries_have_distinct_reports(self):
        directories = [common.generated_directory(name) for name in methods.method_names()]
        self.assertEqual(len(directories), len(set(directories)))

    def test_universal_coverage_requires_its_distinct_audited_gate(self):
        for mutation in ("missing", "unaudited", "duplicate", "nonboolean"):
            entry = copy.deepcopy(methods.api_entries()["LtUInt256UInt64"])
            gate = entry["verification"]
            if mutation == "missing":
                gate.pop("allProfilesTheorem")
            elif mutation == "unaudited":
                gate["allProfilesTheorem"] = "UInt256Proof.Unchecked"
            elif mutation == "duplicate":
                gate["auditedTheorems"] = [gate["auditedTheorems"][0]] * 2
                gate["allProfilesTheorem"] = gate["auditedTheorems"][0]
            else:
                gate["allProfiles"] = 1
            with self.subTest(mutation=mutation), patch.object(methods, "api_entries", return_value={"LtUInt256UInt64": entry}):
                with self.assertRaises(RuntimeError):
                    methods.method_manifest("LtUInt256UInt64")


if __name__ == "__main__":
    unittest.main()
