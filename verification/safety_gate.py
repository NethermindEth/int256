"""Explicit migration registry for combined contracts, never inferred from arithmetic coverage."""

from common import MULTIPLY_PROFILES, PROFILES, expected_profile


MULTIPLY_PRIMITIVES = {
    "OperatorMultiply" + (f"UInt{width}UInt256" if first else f"UInt256UInt{width}"): (width, first)
    for width in (32, 64) for first in (False, True)
}
MULTIPLY_SAFETY_METHODS = {"Multiply", "MultiplyInstance", "OperatorMultiplyUInt256UInt256", *MULTIPLY_PRIMITIVES}


def multiply_safety_module(profile, method="Multiply"):
    flags = expected_profile(profile)
    top = "Avx512" if flags["Avx512DQVL"] else "Avx2" if flags["Avx2"] else "Scalar"
    hardware = flags["Bmi2"] or flags["ArmBase64"]
    word_import = "WordHardwareAudit" if hardware else "WordSoftwareSafety"
    word = ("(fun memory a b output wf writable => hardware_word_invoke memory a b output wf writable "
            "hardware_profile_supported)" if hardware else "software_word_invoke")
    primitive = MULTIPLY_PRIMITIVES.get(method)
    module, theorem = ((f"Primitive{primitive[0]}Safety", f"multiply_primitive{primitive[0]}_contract")
                       if primitive else {"Multiply": ("EntrySafetyContract", "multiply_checked_contract"),
                       "MultiplyInstance": ("InstanceSafety", "multiply_instance_contract"),
                       "OperatorMultiplyUInt256UInt256": ("ReturnSafety", "multiply_return_contract")}[method])
    returning = method == "OperatorMultiplyUInt256UInt256"
    contract = ("ReadOnlyContract (fun values => .v256 ((values[0]?.getD 0) * (values[1]?.getD 0)))"
                if returning else "WrappingBinaryContract (fun left right => left * right)")
    arity = " 2" if returning else ""
    index = "multiplyIndex" if method == "Multiply" else "Extracted.entryIndex"
    binding = ("by\n  simpa only [show multiplyIndex = Extracted.entryIndex from rfl] using checked_contract"
               if method == "Multiply" else "checked_contract")
    reprofile = "ReadOnlyContract" if returning else "WrappingBinaryContract"
    extra_import = ""
    if primitive:
        width, first = primitive
        contract = (f"OrderedScalarContract {str(first).lower()} CIL.Value.i{width}\n"
                    "      (fun input scalar => .v256 (input * BitVec.ofNat 256 scalar.toNat))")
        reprofile = "OrderedScalarContract"
        extra_import = "import UInt256.Safety.OrderedScalarProfiles\n"
    return f"""import UInt256.Methods.Multiply.{module}
{extra_import}import UInt256.Methods.Multiply.SafetyProfiles
import UInt256.Methods.Multiply.FullSafety{top}Top
import UInt256.Methods.Multiply.{word_import}

namespace UInt256Proof.SafetySelected
open UInt256Model.Safety UInt256Proof.Multiply.Safety

theorem checked_contract :
    {contract} Extracted.program {index}{arity} :=
  {theorem} {word} full_{top.lower()}_top

theorem checked_binding :
    {contract} Extracted.program Extracted.entryIndex{arity} := {binding}

theorem checked_family_contract (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.classifyMultiply = profile.classifyMultiply)
    (storage : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    {contract} (CIL.reprofile Extracted.program profile) Extracted.entryIndex{arity} :=
  {reprofile}.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (selected_profile_agreement profile valid same storage) checked_binding

#print axioms checked_contract
#print axioms checked_binding
#print axioms checked_family_contract
end UInt256Proof.SafetySelected
"""


OPERATOR_DESCRIPTORS = {
    f"{polarity}{scalar if first else 'UInt256'}{'UInt256' if first else scalar}":
        (width, signed, first, polarity == "Ne")
    for scalar, width, signed in (("Int32", 32, True), ("UInt32", 32, False),
                                  ("Int64", 64, True), ("UInt64", 64, False))
    for first in (False, True) for polarity in ("Eq", "Ne")
}

COMPARISON_GATES = {
    "LtUInt256UInt256": ("less", "FamilySafetyAudit"),
    "GtUInt256UInt256": ("greater", "GreaterFamilySafetyAudit"),
    "LeUInt256UInt256": ("less_equal", "LessEqualFamilySafetyAudit"),
    "GeUInt256UInt256": ("greater_equal", "GreaterEqualFamilySafetyAudit"),
}

PRIMITIVE_COMPARISONS = {
    f"{relation}{scalar if first else 'UInt256'}{'UInt256' if first else scalar}":
        (width, signed, first, relation)
    for scalar, width, signed in (("Int32", 32, True), ("UInt32", 32, False),
                                  ("Int64", 64, True), ("UInt64", 64, False))
    for first in (False, True) for relation in ("Lt", "Le", "Gt", "Ge")
    # This overload takes UInt256 by value and needs an argument-home contract.
    if not (scalar == "UInt64" and first and relation == "Le")
}


def primitive_comparison_module(method):
    width, signed, first, relation = PRIMITIVE_COMPARISONS[method]
    number = "word.toInt" if signed else "(word.toNat : Int)"
    left, right = (number, "(input.toNat : Int)") if first else ("(input.toNat : Int)", number)
    comparison = f"{left} { {'Lt': '<', 'Le': '≤', 'Gt': '>', 'Ge': '≥'}[relation]} {right}"
    predicate = f"(fun input word => decide ({comparison}))"
    contract = (f"ScalarOperatorContract {str(first).lower()} false CIL.Value.i{width}\n"
                f"      {predicate} Extracted.program Extracted.entryIndex")
    family = contract.replace("Extracted.program", "(CIL.reprofile Extracted.program profile)")
    leaf_first = first != (relation in {"Gt", "Le"})
    negate = relation in {"Le", "Ge"}
    argument = "(widen32 word)" if width == 32 else "word"
    widening = (f", show wrapperSigned32 = {str(signed).lower()} from rfl, widen32, " +
                ("BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)" if signed else
                 "UInt256Proof.Compare.zeroExtend32_toInt")) if width == 32 else ""
    return f"""import UInt256.Methods.Compare.PrimitiveSafetyWrapper{width}
import UInt256.Safety.ScalarOperatorResult
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.SafetySelected
open UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

theorem checked_contract :
    {contract} := by
  have meaning (input : BitVec 256) (word : BitVec {width}) :
      (predicate leafSigned leafScalarFirst input {argument} != wrapperNegate) =
        decide ({comparison}) := by
    simp [show leafSigned = {str(signed or width == 32).lower()} from rfl,
      show leafScalarFirst = {str(leaf_first).lower()} from rfl,
      show wrapperNegate = {str(negate).lower()} from rfl, predicate{widening}] <;>
      (by_cases ordered : {comparison} <;> simp_all <;> omega)
  simpa only [show wrapperScalarFirst = {str(first).lower()} from rfl] using
    ScalarOperatorContract.result_congr meaning checked{width}

theorem checked_binding :
    {contract} := checked_contract

theorem checked_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid) :
    {family} :=
  ScalarOperatorContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (Extracted.program.profile_independent_agreement (by decide) _ _) checked_contract

#print axioms checked_contract
#print axioms checked_binding
#print axioms checked_family_contract
end UInt256Proof.SafetySelected
"""


def operator_safety_module(method, profile):
    """Bind declared order, signedness, width and polarity independently of CIL discovery."""
    width, signed, first, negate = OPERATOR_DESCRIPTORS[method]
    prefix = "Vector" if profile == "x64-vector256" else "Scalar"
    kind = ("S" if signed else "U") + str(width)
    number = "right.toInt" if signed else "(right.toNat : Int)"
    predicate = f"(fun left right => decide ((left.toNat : Int) = {number}))"
    contract = (f"ScalarOperatorContract {str(first).lower()} {str(negate).lower()} CIL.Value.i{width}\n"
                f"      {predicate} Extracted.program Extracted.entryIndex")
    family_contract = contract.replace("Extracted.program", "(CIL.reprofile Extracted.program profile)")
    return f"""import UInt256.Methods.Equality.{prefix}OperatorChild{kind}
import UInt256.Safety.ProfileContracts
import CIL.StorageProfileCoverage

namespace UInt256Proof.SafetySelected
open UInt256Model.Safety UInt256Proof.Equality.Safety

theorem checked_contract :
    {contract} :=
  scalar_operator_checked CIL.Value.i{width} {predicate} (fun _ => rfl) operator_child_checked

theorem checked_binding :
    {contract} := checked_contract

theorem checked_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    {family_contract} := by
  apply ScalarOperatorContract.reprofile
    (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.storage_profile_agreement Extracted.program (by decide) _ _ same)
  exact checked_contract

#print axioms checked_contract
#print axioms checked_binding
#print axioms checked_family_contract
end UInt256Proof.SafetySelected
"""


BITWISE_DESCRIPTORS = {prefix + method: (operation, symbol)
                       for prefix in ("", "Operator")
                       for method, operation, symbol in (("Xor", "xor", "^^^"), ("And", "and", "&&&"), ("Or", "or", "|||"))}
BITWISE_UNARY = {"Not", "OperatorNot"}


def selected_safety_module(method, profile):
    if method in CLASSIFIED_SAFETY_METHODS:
        return classified_safety_module(method, profile)
    if method in MULTIPLY_SAFETY_METHODS:
        return multiply_safety_module(profile, method)
    if method in PRIMITIVE_COMPARISONS:
        return primitive_comparison_module(method)
    if method not in BITWISE_DESCRIPTORS and method not in BITWISE_UNARY:
        return operator_safety_module(method, profile)
    returned = method.startswith("Operator")
    unary = method in BITWISE_UNARY
    scalar = profile == "scalar"
    namespace = "ScalarSafety" if scalar else "NotSafety" if unary else "Safety"
    contract_kind = "ReadOnlyContract" if returned else "InitializedUnaryContract" if unary else "WrappingBinaryContract"
    if unary:
        contract = ("ReadOnlyContract (fun values => .v256 (~~~(values[0]?.getD 0))) "
                    "Extracted.program Extracted.entryIndex 1" if returned else
                    "InitializedUnaryContract (fun input => ~~~input) Extracted.program Extracted.entryIndex")
        module = ("NotScalarReturnSafetyContract" if returned else "NotScalarSafetyContract") if scalar else (
            "NotReturnSafetyContract" if returned else "NotEntrySafety")
        theorem = ("not_return_contract" if scalar else "return_contract") if returned else (
            "not_initialized" if scalar else "vector_entry_initialized")
        index = "scalarIndex" if scalar else "unaryIndex"
        proof = (f"  exact {theorem}" if returned else
                 f"  simpa only [show {index} = Extracted.entryIndex from rfl] using {theorem}")
    else:
        operation, symbol = BITWISE_DESCRIPTORS[method]
        contract = (f"ReadOnlyContract (fun values => .v256 ((values[0]?.getD 0) {symbol} (values[1]?.getD 0))) "
                "Extracted.program Extracted.entryIndex 2" if returned else
                f"WrappingBinaryContract (fun left right => left {symbol} right) Extracted.program Extracted.entryIndex")
        module = ("ScalarReturnSafetyContract" if returned else "ScalarSafetyContract") if scalar else (
            "ReturnSafetyContract" if returned else "VectorEntrySafety")
        theorem = "return_contract" if returned else "scalar_checked" if scalar else "vector_entry_checked"
        index_name = "scalarIndex" if scalar else "binaryIndex"
        index = "" if returned else f", show {index_name} = Extracted.entryIndex from rfl"
        operation_name = "scalarOperation" if scalar else "vectorOperation"
        proof = f"""  have selected : UInt256Model.Bitwise.applyBinary {operation_name} =
      (fun left right : BitVec 256 => left {symbol} right) := by
    funext left right
    simp only [show {operation_name} = .{operation} from rfl, UInt256Model.Bitwise.applyBinary]
  simpa only [selected{index}] using {theorem}"""
    family_contract = contract.replace("Extracted.program", "(CIL.reprofile Extracted.program profile)")
    return f"""import UInt256.Methods.Bitwise.{module}
import UInt256.Safety.ProfileContracts
import CIL.StorageProfileCoverage

namespace UInt256Proof.SafetySelected
open UInt256Model.Safety UInt256Proof.Bitwise.{namespace}

theorem checked_contract : {contract} := by
{proof}

theorem checked_binding : {contract} := checked_contract

theorem checked_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    {family_contract} :=
  {contract_kind}.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.storage_profile_agreement Extracted.program (by decide) _ _ same) checked_contract

#print axioms checked_contract
#print axioms checked_binding
#print axioms checked_family_contract
end UInt256Proof.SafetySelected
"""


def storage_family_coverage(profile):
    return {"kind": "feature-family",
            "condition": "Every valid profile with the same vector256Accelerated flag",
            "family": {"vector256Accelerated": profile == "x64-vector256"}}


def reference_family_coverage(profile):
    vector = profile == "x64-vector256"
    return {"kind": "feature-family",
            "condition": "Every valid profile with the same vector256Accelerated flag and, when false, sse41 flag",
            "family": {"vector256Accelerated": vector,
                       **({} if vector else {"sse41": profile == "x64-sse41"})}}


def comparison_family_coverage(profile):
    if profile == "x64-avx512":
        family = {"avx512FVL": True}
    elif profile == "x64-avx2":
        family = {"avx512FVL": False, "avx2": True}
    else:
        family = {"avx512FVL": False, "avx2": False, "vector256Accelerated": profile == "x64-vector256"}
    condition = ", ".join(f"{flag} {'enabled' if enabled else 'disabled'}" for flag, enabled in family.items())
    return {"kind": "feature-family", "condition": "Every valid profile with " + condition, "family": family}


def representative_safety_gate(method, profile):
    if method in MULTIPLY_SAFETY_METHODS and profile in MULTIPLY_PROFILES:
        return {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety.OrderedScalarContract" if method in MULTIPLY_PRIMITIVES else
                        "UInt256Model.Safety.ReadOnlyContract" if method.startswith("Operator") else
                        "UInt256Model.Safety.WrappingBinaryContract",
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": "+UInt256.Methods.SelectedSafetyGate:olean",
            "theorems": [f"UInt256Proof.SafetySelected.checked_{kind}" for kind in
                         ("contract", "binding", "family_contract")],
            "coverage": {"kind": "feature-family",
                         "condition": "Every valid profile with the same multiplication class and vector256 storage flag"},
            "generatedAudit": True,
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
    shifts = {
        "Lsh": ("", "shift", "shift", False),
        "Rsh": ("Right", "shift", "right_shift", False),
        "LeftShift": ("Wrapper", "wrapper", "wrapper", False),
        "RightShift": ("RightWrapper", "wrapper", "right_wrapper", False),
        "OperatorLsh": ("Return", "return", "return", True),
        "OperatorRsh": ("RightReturn", "return", "right_return", True),
    }
    if method in shifts and profile in {"scalar", "x64-vector256"}:
        audit, contract, binding, returns_value = shifts[method]
        return {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety." + ("ReadOnlyScalarContract" if returns_value else "ShiftContract"),
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": f"+UInt256.Methods.Shift.{audit}SafetyAudit:olean",
            "theorems": [f"UInt256Proof.Shift.Safety.checked_{contract}_contract",
                         f"UInt256Proof.Shift.Safety.checked_{binding}_binding",
                         f"UInt256Proof.Shift.Safety.checked_{binding}_family_binding"],
            "coverage": storage_family_coverage(profile),
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
    static_binary = {
        "AddOverflow": ("UInt256Proof.Safety", "Add.OverflowSafetyAudit", "overflow"),
        "Subtract": ("UInt256Proof.Subtract.Safety", "Subtract.SafetyAudit", "wrapping"),
        "SubtractUnderflow": ("UInt256Proof.Subtract.Safety", "Subtract.UnderflowSafetyAudit", "underflow"),
    }
    vector128_subtract = method in {"Subtract", "SubtractUnderflow"} and profile in {"x64-sse42", "arm64-advsimd"}
    sse_overflow = method == "AddOverflow" and profile == "x64-sse42"
    sse_add = method == "Add" and profile == "x64-sse42"
    arm_add = method == "Add" and profile == "arm64-advsimd"
    arm_overflow = method == "AddOverflow" and profile == "arm64-advsimd"
    vector_add = method == "Add" and profile in {"x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"}
    vector_overflow = method == "AddOverflow" and profile in {"x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"}
    vector_subtract = method in {"Subtract", "SubtractUnderflow"} and profile in {"x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"}
    if ((method == "LeUInt64UInt256" or method in static_binary) and profile == "scalar") or vector_subtract or vector_add or vector_overflow or arm_add or arm_overflow or sse_add or sse_overflow or vector128_subtract:
        by_value = method == "LeUInt64UInt256"
        if by_value:
            namespace, target = "UInt256Proof.Compare.PrimitiveValueSafety", "Compare.PrimitiveValueSafetyAudit"
            names = ("checked_contract", "checked_binding", "checked_family_contract")
        elif vector128_subtract:
            namespace = "UInt256Proof.Subtract.Safety"
            operation = "wrapping" if method == "Subtract" else "underflow"
            target = "Subtract.Vector128" + ("SafetyAudit" if method == "Subtract" else "UnderflowSafetyAudit")
            names = (f"checked_vector128_{operation}_contract", f"checked_vector128_{operation}_binding")
        elif sse_overflow:
            namespace, target = "UInt256Proof.Add.Safety", "Add.SSEOverflowSafetyAudit"
            names = ("checked_sse_overflow_contract", "checked_sse_overflow_binding")
        elif sse_add:
            namespace, target = "UInt256Proof.Add.Safety", "Add.SSESafetyAudit"
            names = ("checked_sse_add_contract", "checked_sse_add_binding")
        elif arm_add:
            namespace, target = "UInt256Proof.Add.Safety", "Add.ARMSafetyAudit"
            names = ("checked_arm_add_contract", "checked_arm_add_binding")
        elif arm_overflow:
            namespace, target = "UInt256Proof.Add.Safety", "Add.ARMOverflowSafetyAudit"
            names = ("checked_arm_overflow_contract", "checked_arm_overflow_binding")
        elif vector_overflow:
            namespace, target = "UInt256Proof.Add.Safety", "Add.VectorOverflowSafetyAudit"
            names = ("checked_vector_reporting_contract", "checked_vector_overflow_binding")
        elif vector_add:
            namespace, target = "UInt256Proof.Add.Safety", "Add.VectorSafetyAudit"
            names = ("checked_vector_parent_contract", "checked_vector_add_binding")
        else:
            namespace, target, operation = static_binary[method]
            if vector_subtract:
                target = f"Subtract.Vector{operation.title()}SafetyAudit"
                operation = "vector_" + operation
            names = (f"checked_{operation}_contract", f"checked_{operation}_binding")
        gate = {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety." + ("ScalarValueContract" if by_value else
                                                   "WrappingBinaryContract" if method in {"Add", "Subtract"} else
                                                   "ReportingBinaryContract"),
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": "+UInt256.Methods." + target + ":olean",
            "theorems": [f"{namespace}.{name}" for name in names],
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
        if by_value:
            gate["coverage"] = {"kind": "all-profiles",
                                "condition": "Every valid profile; actual extracted operations are profile-independent"}
        return gate
    if method in PRIMITIVE_COMPARISONS and profile == "scalar":
        return {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety.ScalarOperatorContract",
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": "+UInt256.Methods.SelectedSafetyGate:olean",
            "theorems": [f"UInt256Proof.SafetySelected.checked_{kind}" for kind in
                         ("contract", "binding", "family_contract")],
            "coverage": {"kind": "all-profiles",
                         "condition": "Every valid profile; actual extracted operations are profile-independent"},
            "generatedAudit": True,
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
    if method in {"CompareToUInt256Ref", "CompareToUInt256Value"} and profile == "scalar":
        by_value = method == "CompareToUInt256Value"
        proof = "threeWayValue" if by_value else "threeWay"
        return {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety.ReadOnlyValueContract" if by_value else "UInt256Model.Safety.ReadOnlyContract",
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": f"+UInt256.Methods.Compare.ThreeWay{'Value' if by_value else ''}SafetyAudit:olean",
            "theorems": [f"UInt256Proof.Compare.Safety.checked_{proof}_{kind}"
                         for kind in ("contract", "binding", "family")],
            "coverage": {"kind": "all-profiles",
                         "condition": "Every valid profile; actual extracted operations are profile-independent"},
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
    if method in COMPARISON_GATES and profile in {"scalar", "x64-vector256", "x64-avx2", "x64-avx512"}:
        relation, audit = COMPARISON_GATES[method]
        audit = {"x64-vector256": "Portable", "x64-avx512": "Native"}.get(profile, "") + audit
        return {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety.ReadOnlyContract",
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": f"+UInt256.Methods.Compare.{audit}:olean",
            "theorems": [f"UInt256Proof.Compare.Safety.checked_{relation}_{kind}"
                         for kind in ("contract", "binding", "family")],
            "coverage": comparison_family_coverage(profile),
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
    if (method in BITWISE_DESCRIPTORS or method in BITWISE_UNARY) and profile in {"scalar", "x64-vector256"}:
        return {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety.ReadOnlyContract" if method.startswith("Operator") else
                        "UInt256Model.Safety.InitializedUnaryContract" if method in BITWISE_UNARY else
                        "UInt256Model.Safety.WrappingBinaryContract",
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": "+UInt256.Methods.SelectedSafetyGate:olean",
            "theorems": [f"UInt256Proof.SafetySelected.checked_{kind}" for kind in
                         ("contract", "binding", "family_contract")],
            "coverage": storage_family_coverage(profile),
            "generatedAudit": True,
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
    if method in OPERATOR_DESCRIPTORS and profile in {"scalar", "x64-vector256"}:
        return {
            "semanticsVersion": "cil-allocation-safety-1",
            "contract": "UInt256Model.Safety.ScalarOperatorContract",
            "callingConditions": "UInt256Model.Safety.CallingConditions",
            "target": "+UInt256.Methods.SelectedSafetyGate:olean",
            "theorems": ["UInt256Proof.SafetySelected.checked_contract", "UInt256Proof.SafetySelected.checked_binding",
                         "UInt256Proof.SafetySelected.checked_family_contract"],
            "coverage": storage_family_coverage(profile),
            "generatedAudit": True,
            "profile": profile,
            "method": method,
            "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
        }
    equality_methods = {"EqUInt256UInt256", "EqualsUInt256Ref", "NeUInt256UInt256", "EqualsUInt256Value"}
    vector = method in {*equality_methods, "EqualsUInt64", "EqualsUInt32", "EqualsInt64", "EqualsInt32"} and profile == "x64-vector256"
    sse = method in equality_methods and profile == "x64-sse41"
    primitive = method in {"EqualsUInt64", "EqualsUInt32"}
    signed = method in {"EqualsInt64", "EqualsInt32"}
    scalar = profile == "scalar" and (method in {"Add", *equality_methods} or primitive or signed)
    if not (scalar or vector or sse):
        raise RuntimeError(f"Combined safety proof not yet available: {method}/{profile}")
    equality = method != "Add"
    inequality = method == "NeUInt256UInt256"
    by_value = method == "EqualsUInt256Value"
    namespace = "UInt256Proof.Equality.Safety" if equality else "UInt256Proof.Safety"
    theorem = "checked_inequality" if inequality else "checked_equality" if equality else "checked_add"
    audit = ("VectorNegationSafetyAudit" if inequality else "VectorSafetyAudit") if vector else (
        "NegationSafetyAudit" if inequality else "SafetyAudit")
    if sse:
        audit = "SseNegationSafetyAudit" if inequality else "SseSafetyAudit"
    if by_value:
        theorem = "checked_value"
        audit = ("Vector" if vector else "Sse" if sse else "") + "ValueSafetyAudit"
    contract = "ReadOnlyValueContract" if by_value else "ReadOnlyContract" if equality else "WrappingBinaryContract"
    if primitive:
        theorem, audit, contract = "checked_primitive", "PrimitiveSafetyAudit", "ReadOnlyScalarContract"
        if method == "EqualsUInt32":
            audit = "Primitive32SafetyAudit"
        if vector:
            audit = "VectorPrimitive64SafetyAudit" if method == "EqualsUInt64" else "VectorPrimitive32SafetyAudit"
    if signed:
        theorem, contract = "checked_signed", "ReadOnlyScalarContract"
        audit = "Signed64SafetyAudit" if method == "EqualsInt64" else "Signed32SafetyAudit"
        if vector:
            audit = "Vector" + audit
    gate = {
        "semanticsVersion": "cil-allocation-safety-1",
        "contract": f"UInt256Model.Safety.{contract}",
        "callingConditions": "UInt256Model.Safety.CallingConditions",
        "target": f"+UInt256.Methods.{'Equality' if equality else 'Add'}.{audit}:olean",
        "theorems": [f"{namespace}.{theorem}_contract", f"{namespace}.{theorem}_binding"],
        "profile": profile,
        "method": method,
        "runtimeBoundary": "Tracked managed references; no native-code, GC-root-map or concurrency proof",
    }
    if primitive or signed:
        gate["theorems"].append(f"{namespace}.{theorem}_family")
        gate["coverage"] = storage_family_coverage(profile)
    elif method in equality_methods:
        gate["theorems"].append(f"{namespace}.{theorem}_family")
        gate["coverage"] = reference_family_coverage(profile)
    return gate


CLASSIFIED_SAFETY_METHODS = {"Add", "Subtract", "AddOverflow", "SubtractUnderflow"}


def classified_safety_module(method, profile):
    base = representative_safety_gate(method, profile)
    module = base["target"].removeprefix("+").split(":")[0]
    reporting = method in {"AddOverflow", "SubtractUnderflow"}
    adding = method in {"Add", "AddOverflow"}
    kind = "ReportingBinaryContract" if reporting else "WrappingBinaryContract"
    contract = f"{kind} (fun left right => left {'+' if adding else '-'} right)"
    if reporting:
        flag = "2^256 ≤ left.toNat + right.toNat" if adding else "left.toNat < right.toNat"
        contract += f"\n      (fun left right => decide ({flag}))"
    return f"""import {module}
import UInt256.Safety.ReportingContract

namespace UInt256Proof.SafetySelected
open UInt256Model.Safety

theorem checked_family_contract (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : profile.classify = Extracted.profile.classify) :
    {contract} (CIL.reprofile Extracted.program profile) Extracted.entryIndex :=
  {kind}.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.Program.same_family_profile_agreement _ _ _ valid Extracted.profileValid same
      (CIL.Program.classified_of_check _ _ (by decide)))
    {base['theorems'][-1]}

#print axioms checked_family_contract
end UInt256Proof.SafetySelected
"""


def safety_gate(method, profile):
    gate = representative_safety_gate(method, profile)
    gate["alignmentPolicy"] = {
        "id": "coreclr-x64-arm64-ordinary-1",
        "ordinaryAccessBytes": 1,
        "targetArchitectures": ["x64", "arm64"],
        "memory": "Normal managed, stack and immutable static storage; alignment traps disabled",
        "excluded": ["aligned memory APIs", "volatile or atomic accesses", "device memory"],
        "portableCliGuarantee": False,
        "runtimeSourceEvidence": "dotnet/runtime@4271d88e0aebf3d04f188f1334c2220d80555ef6",
        "boundary": "verification/CIL/Safety/ALIGNMENT.md",
    }
    gate["modelLimitations"] = [{
        "kind": "instruction-alignment", "status": "target-runtime-assumption",
        "detail": "Ordinary byte-aligned accesses use the stated CoreCLR memory convention; JIT correspondence is not kernel-proved",
        "boundary": "verification/CIL/Safety/ALIGNMENT.md",
    }]
    if method in CLASSIFIED_SAFETY_METHODS and profile in PROFILES:
        gate = {**gate, "target": "+UInt256.Methods.SelectedSafetyGate:olean", "generatedAudit": True,
                "theorems": [*gate["theorems"], "UInt256Proof.SafetySelected.checked_family_contract"],
                "coverage": {"kind": "feature-family",
                             "condition": "Every valid profile with the same checked FeatureClass"}}
    return gate
