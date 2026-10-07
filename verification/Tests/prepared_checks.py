"""Reject stale shared build bundles before and after per-profile proof checking."""

from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common
from common import representative_safety_gate, OPERATOR_DESCRIPTORS, PRIMITIVE_COMPARISONS, selected_safety_module, PROFILES, MULTIPLY_PROFILES, VERIFY, source_files


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

    def test_all_production_gate_imports_resolve(self):
        from common import audit_module, api_entries, LEGACY, method_names
        from common import safety_gate
        from common import coverage_plan

        seen = set()
        def visit(module, text=None):
            if module == "Extracted" or module.split(".")[0] in {"Lean", "Std", "Init"}:
                return
            if text is None:
                if module in seen:
                    return
                seen.add(module)
                path = VERIFY / (module.replace(".", "/") + ".lean")
                self.assertTrue(path.is_file(), module)
                text = path.read_text(encoding="utf-8")
            for imported in re.findall(r"^import (\S+)", text, re.M):
                visit(imported)

        for method, profile in coverage_plan(method_names(), safety=True):
            with self.subTest(method=method, profile=profile):
                if method in LEGACY:
                    visit("Audit" if method == "Add" else "SubtractAudit")
                else:
                    visit("SelectedGate", audit_module(api_entries()[method]))
                gate = safety_gate(method, profile)
                if gate.get("generatedAudit"):
                    visit("SelectedSafetyGate", selected_safety_module(method, profile))
                else:
                    visit(gate["target"].removeprefix("+").removesuffix(":olean"))

    def test_cil_imports_do_not_depend_on_the_consumer(self):
        for path in source_files(VERIFY / "CIL", {".lean"}):
            imports = re.findall(r"^import (\S+)", path.read_text(encoding="utf-8"), re.M)
            self.assertFalse([name for name in imports if name.startswith(("UInt256", "Extracted"))], path)

    def test_editor_layout_is_not_a_verification_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ("Code.cs", "manifest.json", ".vs/v17/DocumentLayout.json", ".vs/Generated.cs"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("test input", encoding="utf-8")
            self.assertEqual({path.relative_to(root).as_posix()
                              for path in source_files(root, {".cs", ".json"})},
                             {"Code.cs", "manifest.json"})

    def test_safety_reports_expose_target_alignment_boundary(self):
        for method in ("Add", "EqualsUInt64", "CompareToUInt256Ref", "Lsh", "Multiply"):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "scalar")
                limitation = gate["modelLimitations"][0]
                self.assertEqual(limitation["kind"], "instruction-alignment")
                self.assertEqual(limitation["status"], "target-runtime-assumption")
                policy = gate["alignmentPolicy"]
                self.assertEqual(policy["ordinaryAccessBytes"], 1)
                self.assertEqual(policy["targetArchitectures"], ["x64", "arm64"])
                self.assertFalse(policy["portableCliGuarantee"])
                self.assertIn("aligned memory APIs", policy["excluded"])

    def test_classified_safety_requires_representative_and_family_audits(self):
        for method in ("Add", "Subtract", "AddOverflow", "SubtractUnderflow"):
            for profile in PROFILES:
                with self.subTest(method=method, profile=profile):
                    gate = common.safety_gate(method, profile)
                    base = representative_safety_gate(method, profile)
                    self.assertEqual(gate["target"], "+UInt256.Methods.SelectedSafetyGate:olean")
                    self.assertTrue(gate["generatedAudit"])
                    self.assertEqual(gate["theorems"], base["theorems"] +
                                     ["UInt256Proof.SafetySelected.checked_family_contract"])
                    self.assertEqual(gate["coverage"]["kind"], "feature-family")
                    source = selected_safety_module(method, profile)
                    self.assertIn("import " + base["target"][1:].split(":")[0], source)
                    self.assertIn(base["theorems"][-1], source)
                    self.assertIn("same_family_profile_agreement", source)
                    self.assertIn("profile.classify = Extracted.profile.classify", source)
                    for omitted in gate["theorems"]:
                        output = "\n".join(f"'{name}' depends on axioms: []"
                                           for name in gate["theorems"] if name != omitted)
                        with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                            common.theorem_audits(output, gate["theorems"], [])

    def test_multiply_requires_bound_contract_and_family_audits(self):
        for method in ("Multiply", "MultiplyInstance", "OperatorMultiplyUInt256UInt256",
                       "OperatorMultiplyUInt256UInt32", "OperatorMultiplyUInt32UInt256",
                       "OperatorMultiplyUInt256UInt64", "OperatorMultiplyUInt64UInt256"):
            for profile in MULTIPLY_PROFILES:
                with self.subTest(method=method, profile=profile):
                    gate = common.safety_gate(method, profile)
                    contract = ("OrderedScalarContract" if "UInt32" in method or "UInt64" in method else
                                "ReadOnlyContract" if method.startswith("Operator") else "WrappingBinaryContract")
                    self.assertEqual(gate["contract"], "UInt256Model.Safety." + contract)
                    self.assertTrue(gate["generatedAudit"])
                    if contract == "OrderedScalarContract":
                        width = 32 if "UInt32" in method else 64
                        first = method.startswith(f"OperatorMultiplyUInt{width}")
                        source = selected_safety_module(method, profile)
                        self.assertIn(f"OrderedScalarContract {str(first).lower()} CIL.Value.i{width}", source)
                        self.assertIn("input * BitVec.ofNat 256 scalar.toNat", source)
                        self.assertIn("OrderedScalarContract.reprofile", source)
                    for omitted in gate["theorems"]:
                        output = "\n".join(f"'{name}' depends on axioms: []"
                                           for name in gate["theorems"] if name != omitted)
                        with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                            common.theorem_audits(output, gate["theorems"], [])
        for method, profile in (("OperatorMultiplyUInt256UInt64", "x64-sse41"), ("Multiply", "x64-sse41")):
            with self.assertRaisesRegex(RuntimeError, "not yet available"):
                common.safety_gate(method, profile)

    def test_primitive_comparisons_require_exact_contract_and_family_audits(self):
        expected = {relation + operands
                    for scalar in ("Int32", "UInt32", "Int64", "UInt64")
                    for operands in (scalar + "UInt256", "UInt256" + scalar)
                    for relation in ("Lt", "Le", "Gt", "Ge")} - {"LeUInt64UInt256"}
        self.assertEqual(set(PRIMITIVE_COMPARISONS), expected)
        for method in expected:
            with self.subTest(method=method):
                gate = common.safety_gate(method, "scalar")
                self.assertEqual(gate["contract"], "UInt256Model.Safety.ScalarOperatorContract")
                self.assertEqual(gate["coverage"]["kind"], "all-profiles")
                self.assertTrue(gate["generatedAudit"])
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])
        # A by-value argument must never silently receive the reference contract.
        value = common.safety_gate("LeUInt64UInt256", "scalar")
        self.assertEqual(value["contract"], "UInt256Model.Safety.ScalarValueContract")
        self.assertEqual(value["coverage"]["kind"], "all-profiles")
        self.assertNotIn("generatedAudit", value)
        output = "\n".join(f"'{name}' depends on axioms: []" for name in value["theorems"][:-1])
        with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
            common.theorem_audits(output, value["theorems"], [])

    def test_add_vector_safety_requires_exact_public_audits(self):
        gate = representative_safety_gate("Add", "x64-avx2")
        self.assertEqual(gate["contract"], "UInt256Model.Safety.WrappingBinaryContract")
        self.assertEqual(gate["target"], "+UInt256.Methods.Add.VectorSafetyAudit:olean")
        self.assertEqual(gate["theorems"], ["UInt256Proof.Add.Safety.checked_vector_parent_contract",
                                           "UInt256Proof.Add.Safety.checked_vector_add_binding"])
        self.assertNotIn("coverage", gate)
        for missing in gate["theorems"]:
            output = "\n".join(f"'{name}' depends on axioms: []"
                               for name in gate["theorems"] if name != missing)
            with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                common.theorem_audits(output, gate["theorems"], [])
        for profile in ("x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"):
            selected = representative_safety_gate("Add", profile)
            self.assertEqual(selected["theorems"], gate["theorems"])
            self.assertEqual(selected["profile"], profile)
            self.assertNotIn("coverage", selected)
        for profile in ("x64-sse41", "x64-vector256"):
            with self.assertRaisesRegex(RuntimeError, "not yet available"):
                representative_safety_gate("Add", profile)

    def test_vector128_add_safety_requires_exact_public_binding(self):
        for isa, profile in (("arm", "arm64-advsimd"), ("sse", "x64-sse42")):
            gate = representative_safety_gate("Add", profile)
            self.assertEqual(gate["contract"], "UInt256Model.Safety.WrappingBinaryContract")
            self.assertEqual(gate["target"], f"+UInt256.Methods.Add.{isa.upper()}SafetyAudit:olean")
            self.assertEqual(gate["theorems"], [f"UInt256Proof.Add.Safety.checked_{isa}_add_contract",
                                               f"UInt256Proof.Add.Safety.checked_{isa}_add_binding"])
            self.assertEqual(gate["profile"], profile)
            self.assertNotIn("coverage", gate)
            for missing in gate["theorems"]:
                output = "\n".join(f"'{name}' depends on axioms: []"
                                   for name in gate["theorems"] if name != missing)
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])

    def test_vector128_subtraction_requires_exact_public_bindings(self):
        for method, operation, audit in (("Subtract", "wrapping", "SafetyAudit"),
                                         ("SubtractUnderflow", "underflow", "UnderflowSafetyAudit")):
            for profile in ("x64-sse42", "arm64-advsimd"):
                with self.subTest(method=method, profile=profile):
                    gate = representative_safety_gate(method, profile)
                    contract = "WrappingBinaryContract" if method == "Subtract" else "ReportingBinaryContract"
                    self.assertEqual(gate["contract"], "UInt256Model.Safety." + contract)
                    self.assertEqual(gate["target"], f"+UInt256.Methods.Subtract.Vector128{audit}:olean")
                    self.assertEqual(gate["theorems"], [f"UInt256Proof.Subtract.Safety.checked_vector128_{operation}_{kind}"
                                                       for kind in ("contract", "binding")])
                    self.assertEqual(gate["profile"], profile)
                    self.assertNotIn("coverage", gate)
                    for missing in gate["theorems"]:
                        output = "\n".join(f"'{name}' depends on axioms: []"
                                           for name in gate["theorems"] if name != missing)
                        with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                            common.theorem_audits(output, gate["theorems"], [])

    def test_vector128_overflow_requires_exact_reporting_binding(self):
        for isa, profile in (("arm", "arm64-advsimd"), ("sse", "x64-sse42")):
            gate = representative_safety_gate("AddOverflow", profile)
            self.assertEqual(gate["contract"], "UInt256Model.Safety.ReportingBinaryContract")
            self.assertEqual(gate["target"], f"+UInt256.Methods.Add.{isa.upper()}OverflowSafetyAudit:olean")
            self.assertEqual(gate["theorems"], [f"UInt256Proof.Add.Safety.checked_{isa}_overflow_contract",
                                               f"UInt256Proof.Add.Safety.checked_{isa}_overflow_binding"])
            self.assertEqual(gate["profile"], profile)
            self.assertNotIn("coverage", gate)
            for missing in gate["theorems"]:
                output = "\n".join(f"'{name}' depends on axioms: []"
                                   for name in gate["theorems"] if name != missing)
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])

    def test_reporting_requires_result_and_flag_binding_for_selected_profile(self):
        for method, namespace, operation in (
            ("AddOverflow", "UInt256Proof.Safety", "overflow"),
            ("SubtractUnderflow", "UInt256Proof.Subtract.Safety", "underflow"),
        ):
            with self.subTest(method=method):
                gate = representative_safety_gate(method, "scalar")
                self.assertEqual(gate["contract"], "UInt256Model.Safety.ReportingBinaryContract")
                self.assertEqual(gate["theorems"], [f"{namespace}.checked_{operation}_contract",
                                                   f"{namespace}.checked_{operation}_binding"])
                self.assertNotIn("coverage", gate)
                output = f"'{gate['theorems'][0]}' depends on axioms: []"
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                    common.theorem_audits(output, gate["theorems"], [])

    def test_vector_underflow_requires_result_flag_and_binding(self):
        for profile in ("x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"):
            gate = representative_safety_gate("SubtractUnderflow", profile)
            self.assertEqual(gate["contract"], "UInt256Model.Safety.ReportingBinaryContract")
            self.assertEqual(gate["target"], "+UInt256.Methods.Subtract.VectorUnderflowSafetyAudit:olean")
            self.assertEqual(gate["theorems"], ["UInt256Proof.Subtract.Safety.checked_vector_underflow_contract",
                                               "UInt256Proof.Subtract.Safety.checked_vector_underflow_binding"])
            self.assertNotIn("coverage", gate)
            with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                common.theorem_audits(f"'{gate['theorems'][0]}' depends on axioms: []", gate["theorems"], [])
        with self.assertRaisesRegex(RuntimeError, "not yet available"):
            representative_safety_gate("AddOverflow", "arm64")

    def test_vector_overflow_requires_exact_result_and_flag_contract(self):
        for profile in ("x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"):
            with self.subTest(profile=profile):
                gate = representative_safety_gate("AddOverflow", profile)
                self.assertEqual(gate["profile"], profile)
                self.assertEqual(gate["contract"], "UInt256Model.Safety.ReportingBinaryContract")
                self.assertEqual(gate["target"], "+UInt256.Methods.Add.VectorOverflowSafetyAudit:olean")
                self.assertEqual(gate["theorems"], ["UInt256Proof.Add.Safety.checked_vector_reporting_contract",
                                                   "UInt256Proof.Add.Safety.checked_vector_overflow_binding"])
                self.assertNotIn("coverage", gate)
                for missing in gate["theorems"]:
                    output = "\n".join(f"'{name}' depends on axioms: []"
                                       for name in gate["theorems"] if name != missing)
                    with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
                        common.theorem_audits(output, gate["theorems"], [])

    def test_wrapping_subtract_uses_void_contract_and_exact_binding(self):
        gate = representative_safety_gate("Subtract", "scalar")
        self.assertEqual(gate["contract"], "UInt256Model.Safety.WrappingBinaryContract")
        self.assertEqual(gate["target"], "+UInt256.Methods.Subtract.SafetyAudit:olean")
        self.assertEqual(gate["theorems"], ["UInt256Proof.Subtract.Safety.checked_wrapping_contract",
                                           "UInt256Proof.Subtract.Safety.checked_wrapping_binding"])
        self.assertNotIn("coverage", gate)
        vector = representative_safety_gate("Subtract", "x64-avx2")
        self.assertEqual(vector["contract"], gate["contract"])
        self.assertEqual(vector["target"], "+UInt256.Methods.Subtract.VectorWrappingSafetyAudit:olean")
        self.assertEqual(vector["theorems"], ["UInt256Proof.Subtract.Safety.checked_vector_wrapping_contract",
                                             "UInt256Proof.Subtract.Safety.checked_vector_wrapping_binding"])
        self.assertNotIn("coverage", vector)
        bmi = representative_safety_gate("Subtract", "x64-avx2-bmi1")
        self.assertEqual(bmi["theorems"], vector["theorems"])
        self.assertEqual(bmi["target"], vector["target"])
        self.assertEqual(bmi["profile"], "x64-avx2-bmi1")
        self.assertNotIn("coverage", bmi)
        for profile in ("x64-sse41", "x64-vector256"):
            with self.assertRaisesRegex(RuntimeError, "not yet available"):
                representative_safety_gate("Subtract", profile)
        output = f"'{gate['theorems'][0]}' depends on axioms: []"
        with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit"):
            common.theorem_audits(output, gate["theorems"], [])

    def test_unsigned32_comparison_keeps_unsigned_public_meaning_through_signed_helper(self):
        source = selected_safety_module("GtUInt256UInt32", "scalar")
        self.assertIn("decide ((input.toNat : Int) > (word.toNat : Int))", source)
        self.assertIn("show wrapperSigned32 = false from rfl", source)
        self.assertIn("show leafSigned = true from rfl", source)
        self.assertIn("UInt256Proof.Compare.zeroExtend32_toInt", source)

    def test_three_way_safety_requires_checked_profile_independence(self):
        gate = common.safety_gate("CompareToUInt256Ref", "scalar")
        self.assertEqual(gate["target"], "+UInt256.Methods.Compare.ThreeWaySafetyAudit:olean")
        self.assertEqual(gate["coverage"]["kind"], "all-profiles")
        self.assertEqual(gate["theorems"], [f"UInt256Proof.Compare.Safety.checked_threeWay_{kind}"
                                           for kind in ("contract", "binding", "family")])
        output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
        with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
            common.theorem_audits(output, gate["theorems"], [])
        value = common.safety_gate("CompareToUInt256Value", "scalar")
        self.assertEqual(value["contract"], "UInt256Model.Safety.ReadOnlyValueContract")
        self.assertEqual(value["target"], "+UInt256.Methods.Compare.ThreeWayValueSafetyAudit:olean")
        self.assertEqual(value["theorems"], [name.replace("threeWay", "threeWayValue") for name in gate["theorems"]])
        self.assertEqual(value["coverage"], gate["coverage"])
        value_output = "\n".join(f"'{name}' depends on axioms: []" for name in value["theorems"][:-1])
        with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
            common.theorem_audits(value_output, value["theorems"], [])

    def test_comparison_safety_requires_its_exact_migrated_entry_and_profile(self):
        gate = common.safety_gate("LtUInt256UInt256", "scalar")
        self.assertEqual(gate["target"], "+UInt256.Methods.Compare.FamilySafetyAudit:olean")
        self.assertEqual(gate["contract"], "UInt256Model.Safety.ReadOnlyContract")
        self.assertEqual(gate["theorems"], ["UInt256Proof.Compare.Safety.checked_less_contract",
                                           "UInt256Proof.Compare.Safety.checked_less_binding",
                                           "UInt256Proof.Compare.Safety.checked_less_family"])
        self.assertEqual(gate["coverage"]["family"],
                         {"avx512FVL": False, "avx2": False, "vector256Accelerated": False})
        greater = common.safety_gate("GtUInt256UInt256", "scalar")
        self.assertEqual(greater["target"], "+UInt256.Methods.Compare.GreaterFamilySafetyAudit:olean")
        self.assertEqual(greater["theorems"], [name.replace("less", "greater") for name in gate["theorems"]])
        self.assertEqual(greater["coverage"], gate["coverage"])
        for method, profile in (("LtUInt256UInt256", "arm64"),
                                ("GtUInt256UInt256", "arm64"),
                                ("LeUInt64UInt256", "x64-vector256")):
            with self.subTest(method=method, profile=profile):
                with self.assertRaisesRegex(RuntimeError, "not yet available"):
                    common.safety_gate(method, profile)

    def test_portable_comparisons_require_checked_family_audits(self):
        for method in ("LtUInt256UInt256", "GtUInt256UInt256", "LeUInt256UInt256", "GeUInt256UInt256"):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "x64-vector256")
                scalar = common.safety_gate(method, "scalar")
                self.assertEqual(gate["target"], scalar["target"].replace("Compare.", "Compare.Portable"))
                self.assertEqual(gate["theorems"], scalar["theorems"])
                self.assertEqual(gate["coverage"]["family"],
                                 {"avx512FVL": False, "avx2": False, "vector256Accelerated": True})
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
                    common.theorem_audits(output, gate["theorems"], [])
                for profile in ("arm64",):
                    with self.assertRaisesRegex(RuntimeError, "not yet available"):
                        common.safety_gate(method, profile)

    def test_avx2_comparisons_use_checked_scalar_dispatch_family(self):
        for method in ("LtUInt256UInt256", "GtUInt256UInt256", "LeUInt256UInt256", "GeUInt256UInt256"):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "x64-avx2")
                scalar = common.safety_gate(method, "scalar")
                self.assertEqual(gate["target"], scalar["target"])
                self.assertEqual(gate["theorems"], scalar["theorems"])
                self.assertEqual(gate["coverage"]["family"], {"avx512FVL": False, "avx2": True})
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
                    common.theorem_audits(output, gate["theorems"], [])

    def test_native_comparisons_require_their_own_family_proofs(self):
        for method in ("LtUInt256UInt256", "GtUInt256UInt256", "LeUInt256UInt256", "GeUInt256UInt256"):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "x64-avx512")
                scalar = common.safety_gate(method, "scalar")
                self.assertEqual(gate["target"], scalar["target"].replace("Compare.", "Compare.Native"))
                self.assertEqual(gate["theorems"], scalar["theorems"])
                self.assertEqual(gate["coverage"]["family"], {"avx512FVL": True})
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
                    common.theorem_audits(output, gate["theorems"], [])

    def test_inclusive_comparisons_require_their_own_contracts_and_family_audits(self):
        for method, relation, module in (("LeUInt256UInt256", "less_equal", "LessEqual"),
                                         ("GeUInt256UInt256", "greater_equal", "GreaterEqual")):
            with self.subTest(method=method):
                gate = common.safety_gate(method, "scalar")
                self.assertEqual(gate["target"], f"+UInt256.Methods.Compare.{module}FamilySafetyAudit:olean")
                self.assertEqual(gate["theorems"], [f"UInt256Proof.Compare.Safety.checked_{relation}_{kind}"
                                                   for kind in ("contract", "binding", "family")])
                output = "\n".join(f"'{name}' depends on axioms: []" for name in gate["theorems"][:-1])
                with self.assertRaisesRegex(RuntimeError, "Missing or ambiguous theorem axiom audit.*_family"):
                    common.theorem_audits(output, gate["theorems"], [])
                with self.assertRaisesRegex(RuntimeError, "not yet available"):
                    common.safety_gate(method, "arm64")

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
