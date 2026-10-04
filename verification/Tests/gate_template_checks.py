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


class ReturningBitwiseGateChecks(unittest.TestCase):
    def test_return_contract_and_operation_for_every_operator(self):
        for name, operation in (("OperatorXor", "xor"), ("OperatorAnd", "and"),
                                ("OperatorOr", "or"), ("OperatorNot", "not")):
            with self.subTest(api=name):
                entry = copy.deepcopy(api_entries()[name])
                text = audit_module(entry)
                if operation == "not":
                    self.assertIn("Bitwise.NotReturnContract", text)
                    self.assertIn("not_bitwise_return_execute initial, input", text)
                else:
                    self.assertIn(f"Extracted.entryIndex .{operation}", text)
                    self.assertIn(f"Bitwise.value_{operation}", text)
                self.assertIn("#print axioms checked_family_contract", text)
                self.assertIn("storage_profile_agreement Extracted.program (by decide)", text)

    def test_wrong_operation_return_or_operand_abi_cannot_select_another_contract(self):
        for change in ("operation", "return", "direction", "by-value", "receiver", "injection"):
            with self.subTest(change=change):
                entry = copy.deepcopy(api_entries()["OperatorXor"])
                abi = entry["callingConvention"]
                if change in {"operation", "injection"}:
                    entry["verification"]["template"]["operation"] = "and" if change == "operation" else "xor; sorry"
                elif change == "return":
                    abi["returns"] = "System.Void"
                elif change == "receiver":
                    abi["static"] = False
                else:
                    abi["parameters"][0]["isIn" if change == "direction" else "type"] = False if change == "direction" else "Nethermind.Int256.UInt256"
                with self.assertRaises(RuntimeError):
                    audit_module(entry)


class EqualityGateTemplateChecks(unittest.TestCase):
    def test_width_order_polarity_and_receiver_for_every_primitive_api(self):
        entries = api_entries()
        for scalar, kind, width in (("UInt32", "u32", "W32"), ("UInt64", "u64", "W64"),
                                    ("Int32", "s32", "W32"), ("Int64", "s64", "W64")):
            cases = [(f"Equals{scalar}", False, False)]
            cases += [(f"{op}{left}{right}", first, op == "Ne")
                      for op in ("Eq", "Ne")
                      for left, right, first in (("UInt256", scalar, False), (scalar, "UInt256", True))]
            for name, first, negate in cases:
                with self.subTest(api=name):
                    entry = copy.deepcopy(entries[name])
                    text = audit_module(entry)
                    self.assertIn(f"(word : {width})", text)
                    self.assertIn(f"(.{kind} word) {str(first).lower()} {str(negate).lower()}", text)
                    self.assertIn("Equality.ScalarContract", text)
                    self.assertIn("storage_profile_agreement Extracted.program (by decide)", text)
                    self.assertIn("#print axioms checked_family_contract", text)
                    for key in ("scalarFirst", "instance", "negateResult"):
                        changed = copy.deepcopy(entry)
                        changed["verification"]["template"][key] ^= True
                        with self.subTest(changed=key), self.assertRaises(RuntimeError):
                            audit_module(changed)

    def test_wrong_scalar_embedding_and_descriptor_injection_are_rejected(self):
        for key, value in (("scalarKind", "s64"), ("scalarKind", "u32"),
                           ("scalarKind", "u64; sorry"), ("scalarFirst", 0),
                           ("proof", "sorry")):
            with self.subTest(key=key, value=value):
                entry = copy.deepcopy(api_entries()["EqUInt256UInt64"])
                entry["verification"]["template"][key] = value
                with self.assertRaises(RuntimeError):
                    audit_module(entry)

    def test_mutated_receiver_return_and_operand_abi_are_rejected(self):
        for change in ("receiver", "return", "byValue", "out"):
            with self.subTest(change=change):
                entry = copy.deepcopy(api_entries()["EqUInt256UInt64"])
                abi = entry["callingConvention"]
                if change == "receiver":
                    abi["static"] = False
                elif change == "return":
                    abi["returns"] = "System.Int32"
                elif change == "byValue":
                    abi["parameters"][0]["type"] = "Nethermind.Int256.UInt256"
                else:
                    abi["parameters"][0]["isOut"] = True
                with self.assertRaises(RuntimeError):
                    audit_module(entry)

    def test_profile_independence_requires_a_proof_not_a_descriptor_claim(self):
        entry = copy.deepcopy(api_entries()["EqUInt256UInt64"])
        entry["verification"]["allProfiles"] = True
        with self.assertRaisesRegex(RuntimeError, "Invalid scalar equality"):
            audit_module(entry)


class HandwrittenGateBindingChecks(unittest.TestCase):
    def test_relational_binding_preserves_dispatch_guards_and_arithmetic(self):
        entry = copy.deepcopy(api_entries()["LtUInt256UInt256"])
        gate = entry["verification"]
        theorem = "UInt256Proof.Compare.checked_less_family_contract"
        if theorem not in gate["auditedTheorems"]:
            gate["auditedTheorems"].append(theorem)
        gate["familyCoverage"] = {"kind": "relational-dispatch", "theorem": theorem,
            "representatives": ["scalar", "x64-vector256", "x64-avx2", "x64-avx512"]}
        gate["contract"] = "True"
        text = audit_module(entry)
        self.assertIn("UInt256Model.Compare.Contract (reprofile Extracted.program profile)", text)
        self.assertIn("Extracted.entryIndex .less initial left right", text)
        for guard in ("Extracted.profile.avx512FVL = profile.avx512FVL",
                      "Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2",
                      "Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false → "
                      "Extracted.profile.vector256Accelerated = profile.vector256Accelerated"):
            self.assertIn(guard, text)
        self.assertIn("#print axioms bound_family_contract", text)

    def test_independent_types_bind_selected_and_family_terms(self):
        for name, contract in (("Lsh", "UInt256Proof.Shift.Contract .left"),
                               ("OperatorRsh", "UInt256Proof.Shift.OperatorContract .right"),
                               ("AddOverflow", "UInt256Proof.Reporting.Contract .add"),
                               ("EqualsUInt256Value", "UInt256Model.Equality.SnapshotContract"),
                               ("CompareToUInt256Ref", "UInt256Model.Compare.ThreeWayContract"),
                               ("CompareToUInt256Value", "UInt256Model.Compare.ThreeWaySnapshotContract"),
                               ("Multiply", "UInt256Proof.Multiply.Contract"),
                               ("MultiplyInstance", "UInt256Proof.Multiply.Contract"),
                               ("OperatorMultiplyUInt256UInt256", "UInt256Proof.Multiply.ReturnContract"),
                               ("OperatorMultiplyUInt256UInt64", "UInt256Proof.Multiply.ScalarReturnContract"),
                               ("OperatorMultiplyUInt64UInt256", "UInt256Proof.Multiply.ScalarReturnContract"),
                               ("OperatorMultiplyUInt256UInt32", "UInt256Proof.Multiply.ScalarReturnContract"),
                               ("OperatorMultiplyUInt32UInt256", "UInt256Proof.Multiply.ScalarReturnContract")):
            with self.subTest(api=name):
                entry = copy.deepcopy(api_entries()[name])
                entry["verification"]["contract"] = "True"
                text = audit_module(entry)
                self.assertIn(contract, text)
                self.assertIn("#print axioms bound_contract", text)
                self.assertIn(entry["verification"]["auditedTheorems"][0], text)
                scalar_types = {
                    "OperatorMultiplyUInt256UInt64": (64, "false"),
                    "OperatorMultiplyUInt64UInt256": (64, "true"),
                    "OperatorMultiplyUInt256UInt32": (32, "false"),
                    "OperatorMultiplyUInt32UInt256": (32, "true"),
                }
                if name in scalar_types:
                    width, first = scalar_types[name]
                    self.assertIn(f"(word : W{width})", text)
                    self.assertIn(f"{width} {first} initial input word", text)
                if name in {"CompareToUInt256Value", "EqualsUInt256Value"}:
                    self.assertIn("(right : BitVec 256)", text)
                if entry["verification"].get("familyCoverage"):
                    self.assertIn("#print axioms bound_family_contract", text)
                    self.assertIn(entry["verification"]["familyCoverage"]["theorem"], text)
                else:
                    self.assertIn("#print axioms bound_all_profiles_contract", text)

    def test_handwritten_identifiers_cannot_inject_proofs(self):
        for field in ("auditTarget", "auditedTheorems"):
            entry = copy.deepcopy(api_entries()["Lsh"])
            entry["verification"][field] = "import Bad; sorry" if field == "auditTarget" else ["True.intro; sorry"]
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                audit_module(entry)


if __name__ == "__main__":
    unittest.main()
