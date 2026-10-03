"""Reject a template whose independent contract differs from the selected API."""

import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from gate_templates import audit_module
from methods import api_entries


class GateTemplateChecks(unittest.TestCase):
    def setUp(self):
        self.entry = copy.deepcopy(api_entries()["LtUInt256UInt64"])

    def test_contract_has_declared_width_direction_and_unsigned_number(self):
        text = audit_module(self.entry)
        self.assertIn("(word : W64)", text)
        self.assertIn("(.u64 word) false", text)
        self.assertIn(".less", text)
        self.assertIn("#print axioms checked_profile_contract", text)

    def test_wrong_polarity_width_signedness_or_direction_is_rejected(self):
        for key, value in (("relation", "greater"), ("scalarKind", "u32"),
                           ("scalarKind", "s64"), ("scalarFirst", True)):
            with self.subTest(key=key, value=value):
                entry = copy.deepcopy(self.entry)
                entry["verification"]["template"][key] = value
                with self.assertRaises(RuntimeError):
                    audit_module(entry)


    def test_descriptor_cannot_inject_lean_or_replace_proof(self):
        for key, value in (("relation", "less; sorry"), ("proof", "sorry"), ("scalarFirst", 0)):
            with self.subTest(key=key):
                entry = copy.deepcopy(self.entry)
                entry["verification"]["template"][key] = value
                with self.assertRaisesRegex(RuntimeError, "Invalid scalar comparison"):
                    audit_module(entry)

    def test_by_value_operand_requires_its_own_contract(self):
        self.entry["callingConvention"]["parameters"][0]["type"] = "Nethermind.Int256.UInt256"
        with self.assertRaisesRegex(RuntimeError, "parameter type/direction"):
            audit_module(self.entry)

    def test_malformed_descriptor_fails_explicitly(self):
        for descriptor in (None, [], "scalar-comparison"):
            with self.subTest(descriptor=descriptor):
                entry = copy.deepcopy(self.entry)
                entry["verification"]["template"] = descriptor
                with self.assertRaisesRegex(RuntimeError, "Invalid typed audit descriptor"):
                    audit_module(entry)


class BitwiseGateTemplateChecks(unittest.TestCase):
    def setUp(self):
        self.entry = copy.deepcopy(api_entries()["And"])

    def test_exact_and_contract_and_arithmetic_fact(self):
        text = audit_module(self.entry)
        self.assertIn("Extracted.entryIndex .and", text)
        self.assertIn("UInt256Proof.Bitwise.value_and", text)

    def test_wrong_operation_or_output_direction_is_rejected(self):
        self.entry["verification"]["template"]["operation"] = "or"
        with self.assertRaisesRegex(RuntimeError, "selected operation"):
            audit_module(self.entry)
        self.entry = copy.deepcopy(api_entries()["And"])
        self.entry["callingConvention"]["parameters"][2]["isOut"] = False
        with self.assertRaisesRegex(RuntimeError, "parameter type/direction"):
            audit_module(self.entry)

    def test_independent_profiles_cannot_be_assumed_for_bitwise_template(self):
        self.entry["verification"]["allProfiles"] = True
        with self.assertRaisesRegex(RuntimeError, "Invalid binary bitwise"):
            audit_module(self.entry)


if __name__ == "__main__":
    unittest.main()
