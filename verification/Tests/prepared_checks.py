"""Reject stale shared build bundles before and after per-profile proof checking."""

from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common
from common import OPERATOR_DESCRIPTORS, selected_safety_module


class PreparedBuildChecks(unittest.TestCase):
    def test_runner_bridge_reuses_only_successful_matching_inputs(self):
        revision = ["original"]
        fail = [False]
        commands = []
        def execute(command, **kwargs):
            commands.append(command)
            return subprocess.CompletedProcess(command, 1 if fail[0] else 0, "result", "rejected")
        with patch.object(common, "_runner_inputs", None), patch.object(common, "_runner_outputs", {}), \
             patch.object(common, "sha", side_effect=lambda _: revision[0]), \
             patch.object(common.subprocess, "run", side_effect=execute), \
             patch.object(Path, "is_file", return_value=True):
            request = lambda payload: common._runner_request(["gate", "--entry-json"], payload)
            self.assertEqual(request({"test": 1}), "result")
            self.assertEqual(len(commands), 2)  # Build and first invocation.
            request({"test": 1})
            self.assertEqual(len(commands), 2)
            request({"test": 2})
            self.assertEqual(len(commands), 3)
            revision[0] = "changed source"
            request({"test": 1})
            self.assertEqual(len(commands), 5)
            fail[0] = True
            for _ in range(2):
                with self.assertRaisesRegex(RuntimeError, "rejected"):
                    request({"test": 3})
            self.assertEqual(len(commands), 7)

    def test_bitwise_safety_binds_each_independent_operation(self):
        for method, operation, symbol in (("Xor", "xor", "^^^"), ("And", "and", "&&&"), ("Or", "or", "|||")):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "x64-vector256")
                self.assertEqual(gate["contract"], "UInt256Model.Safety.WrappingBinaryContract")
                self.assertTrue(gate["generatedAudit"])
                self.assertEqual(gate["coverage"]["family"], {"vector256Accelerated": True})
                source = selected_safety_module(method, "x64-vector256")
                self.assertIn(f"left {symbol} right", source)
                self.assertIn(f"vectorOperation = .{operation} from rfl", source)
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])
                with self.assertRaisesRegex(RuntimeError, "not yet available"):
                    common.safety_gate(method, "arm64")

    def test_not_safety_binds_unary_result_and_requires_family_audit(self):
        for method, contract, expression in (
                ("Not", "InitializedUnaryContract", "fun input => ~~~input"),
                ("OperatorNot", "ReadOnlyContract", ".v256 (~~~(values[0]?.getD 0))")):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "x64-vector256")
                self.assertEqual(gate["contract"], f"UInt256Model.Safety.{contract}")
                self.assertEqual(gate["coverage"]["family"], {"vector256Accelerated": True})
                source = selected_safety_module(method, "x64-vector256")
                self.assertIn(expression, source)
                self.assertIn(f"{contract}.reprofile", source)
                self.assertNotIn("vectorOperation", source)
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])
                with self.assertRaisesRegex(RuntimeError, "not yet available"):
                    common.safety_gate(method, "arm64")

    def test_returned_bitwise_operators_bind_values_and_read_only_memory(self):
        for method, symbol in (("OperatorXor", "^^^"), ("OperatorAnd", "&&&"), ("OperatorOr", "|||")):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "x64-vector256")
                self.assertEqual(gate["contract"], "UInt256Model.Safety.ReadOnlyContract")
                source = selected_safety_module(method, "x64-vector256")
                self.assertIn("import UInt256.Methods.Bitwise.ReturnSafetyContract", source)
                self.assertIn(f".v256 ((values[0]?.getD 0) {symbol} (values[1]?.getD 0))", source)
                self.assertIn("using return_contract", source)
                self.assertNotIn("binaryIndex = Extracted.entryIndex", source)
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])
                with self.assertRaisesRegex(RuntimeError, "not yet available"):
                    common.safety_gate(method, "arm64")

    def test_scalar_bitwise_gates_select_checked_constructor_paths(self):
        for method in ("Xor", "And", "Or", "Not", "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot"):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "scalar")
                self.assertEqual(gate["coverage"]["family"], {"vector256Accelerated": False})
                source = selected_safety_module(method, "scalar")
                self.assertIn("UInt256Proof.Bitwise.ScalarSafety", source)
                self.assertNotIn("vectorOperation", source)
                self.assertNotIn("vector_entry", source)
                if not method.startswith("Operator"):
                    self.assertIn("scalarIndex = Extracted.entryIndex from rfl", source)
                if "Not" not in method:
                    self.assertIn(f"scalarOperation = .{method.removeprefix('Operator').lower()} from rfl", source)
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])


    def test_operator_gates_bind_order_signedness_and_polarity(self):
        self.assertEqual(len(OPERATOR_DESCRIPTORS), 16)
        for method, (width, signed, first, negate) in OPERATOR_DESCRIPTORS.items():
            for profile in ("scalar", "x64-vector256"):
                gate = common.safety_gate(method, profile)
                self.assertTrue(gate["generatedAudit"])
                self.assertIn("UInt256Proof.SafetySelected.checked_family_contract", gate["theorems"])
                self.assertEqual(gate["coverage"]["family"],
                                 {"vector256Accelerated": profile == "x64-vector256"})
                source = selected_safety_module(method, profile)
                self.assertIn(f"ScalarOperatorContract {str(first).lower()} {str(negate).lower()} CIL.Value.i{width}", source)
                self.assertIn("right.toInt" if signed else "right.toNat : Int", source)
                self.assertEqual(source.count("#print axioms"), 3)
                self.assertIn("CIL.storage_profile_agreement Extracted.program (by decide)", source)
                self.assertIn("(CIL.reprofile Extracted.program profile)", source)
            with self.assertRaises(RuntimeError):
                common.safety_gate(method, "x64-sse41")


    def test_equality_safety_registry_requires_its_family_audit(self):
        gate = common.safety_gate("EqUInt256UInt256", "scalar")
        self.assertEqual(gate["contract"], "UInt256Model.Safety.ReadOnlyContract")
        self.assertEqual(gate["theorems"], ["UInt256Proof.Equality.Safety.checked_equality_contract",
                                           "UInt256Proof.Equality.Safety.checked_equality_binding",
                                           "UInt256Proof.Equality.Safety.checked_equality_family"])
        with self.assertRaisesRegex(RuntimeError, "not yet available"):
            common.safety_gate("EqUInt256UInt256", "x64-avx2")
        vector = common.safety_gate("EqUInt256UInt256", "x64-vector256")
        self.assertEqual(vector["target"], "+UInt256.Methods.Equality.VectorSafetyAudit:olean")
        self.assertEqual(vector["theorems"], gate["theorems"])
        for method in ("Add", "Subtract", "LtUInt256UInt64"):
            with self.assertRaisesRegex(RuntimeError, "not yet available"):
                common.safety_gate(method, "x64-vector256")
        self.assertEqual(common.safety_gate("NeUInt256UInt256", "x64-vector256")["target"],
                         "+UInt256.Methods.Equality.VectorNegationSafetyAudit:olean")
        self.assertEqual(common.safety_gate("EqualsUInt256Ref", "x64-vector256")["target"], vector["target"])
        for method in ("EqUInt256UInt256", "EqualsUInt256Ref", "NeUInt256UInt256"):
            gate = common.safety_gate(method, "x64-sse41")
            audit = "SseNegationSafetyAudit" if method == "NeUInt256UInt256" else "SseSafetyAudit"
            self.assertEqual(gate["target"], f"+UInt256.Methods.Equality.{audit}:olean")
        with self.assertRaisesRegex(RuntimeError, "not yet available"):
            common.safety_gate("Add", "x64-sse41")


    def test_by_value_safety_has_its_own_contract_and_binding(self):
        for profile, prefix in (("scalar", ""), ("x64-sse41", "Sse"), ("x64-vector256", "Vector")):
            gate = common.safety_gate("EqualsUInt256Value", profile)
            self.assertEqual(gate["contract"], "UInt256Model.Safety.ReadOnlyValueContract")
            self.assertEqual(gate["target"], f"+UInt256.Methods.Equality.{prefix}ValueSafetyAudit:olean")
            self.assertEqual(gate["theorems"], ["UInt256Proof.Equality.Safety.checked_value_contract",
                                               "UInt256Proof.Equality.Safety.checked_value_binding",
                                               "UInt256Proof.Equality.Safety.checked_value_family"])
        with self.assertRaisesRegex(RuntimeError, "not yet available"):
            common.safety_gate("EqualsUInt256Value", "x64-avx2")

    def test_primitive_safety_is_bound_to_selected_scalar_width(self):
        gate = common.safety_gate("EqualsUInt64", "scalar")
        self.assertEqual(gate["contract"], "UInt256Model.Safety.ReadOnlyScalarContract")
        self.assertEqual(gate["target"], "+UInt256.Methods.Equality.PrimitiveSafetyAudit:olean")
        self.assertEqual(gate["theorems"], [
            "UInt256Proof.Equality.Safety.checked_primitive_contract",
            "UInt256Proof.Equality.Safety.checked_primitive_binding",
            "UInt256Proof.Equality.Safety.checked_primitive_family"])
        gate32 = common.safety_gate("EqualsUInt32", "scalar")
        self.assertEqual(gate32["contract"], gate["contract"])
        self.assertEqual(gate32["target"], "+UInt256.Methods.Equality.Primitive32SafetyAudit:olean")
        for method, profile in [("EqualsUInt64", "x64-sse41"), ("EqualsUInt32", "x64-sse41"),
                                ("EqualsInt32", "x64-sse41")]:
            with self.assertRaises(RuntimeError):
                common.safety_gate(method, profile)

    def test_vector_primitive_safety_has_exact_width_gates(self):
        for width in (32, 64):
            gate = common.safety_gate(f"EqualsUInt{width}", "x64-vector256")
            self.assertEqual(gate["contract"], "UInt256Model.Safety.ReadOnlyScalarContract")
            self.assertEqual(gate["target"], f"+UInt256.Methods.Equality.VectorPrimitive{width}SafetyAudit:olean")
            self.assertEqual(gate["profile"], "x64-vector256")

    def test_signed_safety_checks_both_exact_width_bindings(self):
        for width in (32, 64):
            gate = common.safety_gate(f"EqualsInt{width}", "scalar")
            self.assertEqual(gate["contract"], "UInt256Model.Safety.ReadOnlyScalarContract")
            self.assertEqual(gate["target"], f"+UInt256.Methods.Equality.Signed{width}SafetyAudit:olean")
            self.assertEqual(gate["theorems"], [
                "UInt256Proof.Equality.Safety.checked_signed_contract",
                "UInt256Proof.Equality.Safety.checked_signed_binding",
                "UInt256Proof.Equality.Safety.checked_signed_family"])
            vector = common.safety_gate(f"EqualsInt{width}", "x64-vector256")
            self.assertEqual(vector["target"], f"+UInt256.Methods.Equality.VectorSigned{width}SafetyAudit:olean")
            self.assertEqual(vector["theorems"], gate["theorems"])
            with self.assertRaises(RuntimeError):
                common.safety_gate(f"EqualsInt{width}", "x64-sse41")

    def test_shift_families_require_exact_contract_and_bindings(self):
        for method, prefix, contract, binding in (
                ("Lsh", "", "shift", "shift"), ("Rsh", "Right", "shift", "right_shift"),
                ("LeftShift", "Wrapper", "wrapper", "wrapper"),
                ("RightShift", "RightWrapper", "wrapper", "right_wrapper"),
                ("OperatorLsh", "Return", "return", "return"),
                ("OperatorRsh", "RightReturn", "return", "right_return")):
            gate = common.safety_gate(method, "scalar")
            self.assertEqual(gate["contract"], "UInt256Model.Safety." +
                             ("ReadOnlyScalarContract" if contract == "return" else "ShiftContract"))
            self.assertEqual(gate["target"], f"+UInt256.Methods.Shift.{prefix}SafetyAudit:olean")
            self.assertEqual(gate["coverage"]["family"], {"vector256Accelerated": False})
            self.assertEqual(gate["theorems"], [
                f"UInt256Proof.Shift.Safety.checked_{contract}_contract",
                f"UInt256Proof.Shift.Safety.checked_{binding}_binding",
                f"UInt256Proof.Shift.Safety.checked_{binding}_family_binding"])
            vector = common.safety_gate(method, "x64-vector256")
            self.assertEqual(vector["coverage"]["family"], {"vector256Accelerated": True})
            self.assertEqual(vector["theorems"], gate["theorems"])
            for missing in gate["theorems"]:
                output = "\n".join(f"'{name}' depends on axioms: []"
                                   for name in gate["theorems"] if name != missing)
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])
            for profile in ("x64-sse41", "arm64-advsimd"):
                with self.assertRaises(RuntimeError):
                    common.safety_gate(method, profile)

    def test_primitive_instance_families_require_their_own_audits(self):
        for method in ("EqualsUInt32", "EqualsUInt64", "EqualsInt32", "EqualsInt64"):
            for profile in ("scalar", "x64-vector256"):
                gate = common.safety_gate(method, profile)
                self.assertEqual(gate["coverage"]["family"],
                                 {"vector256Accelerated": profile == "x64-vector256"})
                self.assertEqual(len(gate["theorems"]), 3)
                family = gate["theorems"][-1]
                self.assertTrue(family.endswith("_family"))
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
                    common.theorem_audits(output, gate["theorems"], [])

    def test_reference_families_drop_irrelevant_sse_condition_in_vector_mode(self):
        for method in ("EqUInt256UInt256", "EqualsUInt256Ref", "NeUInt256UInt256", "EqualsUInt256Value"):
            for profile in ("scalar", "x64-vector256", "x64-sse41"):
                gate = common.safety_gate(method, profile)
                expected = ({"vector256Accelerated": True} if profile == "x64-vector256" else
                            {"vector256Accelerated": False, "sse41": profile == "x64-sse41"})
                self.assertEqual(gate["coverage"]["family"], expected)
                self.assertEqual(len(gate["theorems"]), 3)
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
                    common.theorem_audits(output, gate["theorems"], [])


if __name__ == "__main__":
    unittest.main()
