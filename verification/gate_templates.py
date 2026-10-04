"""Typed audit modules from explicit, source-hashed public contract descriptors."""

import re

from methods import check_calling_convention


def handwritten_contract(entry):
    """Independent public types; manifest prose is never executable Lean."""
    name = entry["id"]
    variables = "(initial : Bytes) (left right : Nat)"
    prefix = "UInt256Model."
    if name in {"EqUInt256UInt256", "EqualsUInt256Ref", "NeUInt256UInt256"}:
        kind = "InequalityContract" if name.startswith("Ne") else "Contract"
        contract = f"{prefix}Equality.{kind} {{program}} Extracted.entryIndex initial left right"
    elif name == "EqualsUInt256Value":
        variables = "(initial : Bytes) (left : Nat) (right : BitVec 256)"
        contract = f"{prefix}Equality.SnapshotContract {{program}} Extracted.entryIndex initial left right"
    elif name in {"CompareToUInt256Ref", "CompareToUInt256Value"}:
        kind = "ThreeWayContract"
        if name == "CompareToUInt256Value":
            variables = "(initial : Bytes) (left : Nat) (right : BitVec 256)"
            kind = "ThreeWaySnapshotContract"
        contract = f"{prefix}Compare.{kind} {{program}} Extracted.entryIndex initial left right"
    elif name in {"LtUInt256UInt256", "LeUInt256UInt256", "GtUInt256UInt256", "GeUInt256UInt256"}:
        relation = {"Lt": "less", "Le": "lessEqual", "Gt": "greater", "Ge": "greaterEqual"}[name[:2]]
        contract = f"{prefix}Compare.Contract {{program}} Extracted.entryIndex .{relation} initial left right"
    elif name == "LeUInt64UInt256":
        variables = "(initial : Bytes) (word : W64) (right : BitVec 256)"
        contract = (f"{prefix}Compare.ScalarSnapshotContract {{program}} Extracted.entryIndex"
                    " .lessEqual initial (.u64 word) right")
    elif name in {"Not", "Xor"}:
        variables = "(initial : Bytes) (input out : Nat)" if name == "Not" else "(initial : Bytes) (left right out : Nat)"
        contract = (f"{prefix}Bitwise.NotContract {{program}} Extracted.entryIndex initial input out" if name == "Not"
                    else f"{prefix}Bitwise.Contract {{program}} Extracted.entryIndex .xor initial left right out")
    elif name in {"Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"}:
        direction = "left" if name in {"Lsh", "LeftShift", "OperatorLsh"} else "right"
        operator = name.startswith("Operator")
        variables = "(initial : Bytes) (input : Nat) (count : W32)" if operator else "(initial : Bytes) (input out : Nat) (count : W32)"
        kind, arguments = ("OperatorContract", "initial input count") if operator else ("Contract", "initial input out count")
        contract = f"UInt256Proof.Shift.{kind} .{direction} {{program}} Extracted.entryIndex {arguments}"
    elif name in {"AddOverflow", "SubtractUnderflow"}:
        variables = "(initial : Bytes) (left right out : Nat)"
        operation = "add" if name == "AddOverflow" else "subtract"
        contract = f"UInt256Proof.Reporting.Contract .{operation} {{program}} Extracted.entryIndex initial left right out"
    elif name in {"Multiply", "MultiplyInstance"}:
        variables = "(initial : Bytes) (left right out : Nat)"
        contract = "UInt256Proof.Multiply.Contract {program} Extracted.entryIndex initial left right out"
    elif name == "OperatorMultiplyUInt256UInt256":
        contract = "UInt256Proof.Multiply.ReturnContract {program} Extracted.entryIndex initial left right"
    elif name in {"OperatorMultiplyUInt256UInt32", "OperatorMultiplyUInt32UInt256",
                  "OperatorMultiplyUInt256UInt64", "OperatorMultiplyUInt64UInt256"}:
        width = 32 if "UInt32" in name else 64
        word_left = str(name.startswith(f"OperatorMultiplyUInt{width}UInt256")).lower()
        variables = f"(initial : Bytes) (input : Nat) (word : W{width})"
        contract = ("UInt256Proof.Multiply.ScalarReturnContract {program} Extracted.entryIndex "
                    f"{width} {word_left} initial input word")
    else:
        raise RuntimeError(f"No independent typed binding for handwritten API: {name}")
    return variables, contract


def handwritten_bindings(entry):
    gate = entry["verification"]
    variables, contract = handwritten_contract(entry)
    sources = gate["auditedTheorems"]
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", name) for name in sources):
        raise RuntimeError("Invalid handwritten theorem identifier")
    bindings = [("bound_contract", f"∀ {variables}, {contract.format(program='Extracted.program')}", sources[0])]
    profiled = f"∀ {variables}, {contract.format(program='(reprofile Extracted.program profile)')}"
    header = "∀ profile : FeatureProfile, profile.Valid → "
    if gate.get("allProfiles"):
        bindings.append(("bound_all_profiles_contract", header + profiled, gate["allProfilesTheorem"]))
    else:
        family = gate.get("familyCoverage")
        conditional = [name for name in sources[1:] if not family or name != family["theorem"]]
        if len(conditional) > 1:
            raise RuntimeError("Ambiguous handwritten profile binding")
        shift = entry["id"] in {"Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"}
        if conditional:
            proof = (f"by\n  intro profile {'_' if shift else 'valid'} agreement\n"
                     f"  exact {conditional[0]} profile {'agreement' if shift else 'valid agreement'}")
            bindings.append(("bound_profile_contract", header +
                "Extracted.program.ProfileAgreement Extracted.profile profile → " + profiled, proof))
        if family:
            kind = family["kind"]
            guards = {"vector256-storage": "Extracted.profile.vector256Accelerated = profile.vector256Accelerated → ",
                      "vector-reduction": "Extracted.profile.vector256Accelerated = profile.vector256Accelerated → "
                          "(Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) → ",
                      "relational-dispatch": "Extracted.profile.avx512FVL = profile.avx512FVL → "
                          "(Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2) → "
                          "(Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false → "
                          "Extracted.profile.vector256Accelerated = profile.vector256Accelerated) → ",
                      "multiply-dispatch-storage": "Extracted.profile.classifyMultiply = profile.classifyMultiply → "
                          "Extracted.profile.vector256Accelerated = profile.vector256Accelerated → ",
                      "feature-class": "profile.classify = Extracted.profile.classify → "}
            if kind not in guards:
                raise RuntimeError("Unknown handwritten feature family")
            proof = family["theorem"] if not shift else f"by\n  intro profile _ same\n  exact {family['theorem']} profile same"
            bindings.append(("bound_family_contract", header + guards[kind] + profiled, proof))
    return bindings


def bound_audit_names(entry):
    return [f"UInt256Proof.Selected.{name}" for name, _, _ in handwritten_bindings(entry)]


def handwritten_gate(entry):
    target = entry["verification"]["auditTarget"]
    if not re.fullmatch(r"\+[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*:olean", target):
        raise RuntimeError("Invalid handwritten audit module")
    declarations = "\n\n".join(f"theorem {name} : {type_} := {proof}\n#print axioms {name}"
                                for name, type_, proof in handwritten_bindings(entry))
    return (f"import {target[1:-6]}\n\nopen CIL UInt256Model\n"
            "namespace UInt256Proof.Selected\n\n" + declarations + "\n\nend UInt256Proof.Selected\n")


def typed_gate(module, variables, arguments, contract, execution, all_profiles=False, family=False):
    imports = f"import {module}\n"
    if family:
        imports += "import CIL.StorageProfileCoverage\n"
    universal = ""
    if all_profiles:
        universal = f'''
theorem checked_all_profiles_contract : ∀ (profile : FeatureProfile), profile.Valid →
    ∀ {variables},
    {contract.format(program="(reprofile Extracted.program profile)")} := by
  intro profile valid
  apply checked_profile_contract profile valid
  exact Program.profile_independent_agreement Extracted.program (by decide) _ _

#print axioms checked_all_profiles_contract
'''
    if family:
        universal = f'''
theorem checked_family_contract : ∀ (profile : FeatureProfile), profile.Valid →
    Extracted.profile.vector256Accelerated = profile.vector256Accelerated →
    ∀ {variables},
    {contract.format(program="(reprofile Extracted.program profile)")} := by
  intro profile valid same
  apply checked_profile_contract profile valid
  exact CIL.storage_profile_agreement Extracted.program (by decide) _ _ same

#print axioms checked_family_contract
'''
    return f'''{imports}

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Selected

theorem checked_contract : ∀ {variables},
    {contract.format(program="Extracted.program")} := by
  intro {arguments}
  {execution}

theorem checked_profile_contract : ∀ (profile : FeatureProfile), profile.Valid →
    Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ {variables},
    {contract.format(program="(reprofile Extracted.program profile)")} := by
  intro profile _ agreement {arguments}
  obtain ⟨fuel, final, execution, bytes⟩ := checked_contract {arguments}
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← invoke_uniform_reprofile_eq Extracted.program Extracted.profile profile
    (uniform_of_profile_map _ _ Extracted.programProfiles) agreement]
  exact execution

#print axioms checked_contract
#print axioms checked_profile_contract
{universal}
end UInt256Proof.Selected
'''


def scalar_comparison_gate(entry):
    descriptor = entry["verification"]["template"]
    relations = {"less": "op_LessThan", "lessEqual": "op_LessThanOrEqual",
                 "greater": "op_GreaterThan", "greaterEqual": "op_GreaterThanOrEqual"}
    kinds = {"u32": ("W32", "System.UInt32"), "u64": ("W64", "System.UInt64"),
             "s32": ("W32", "System.Int32"), "s64": ("W64", "System.Int64")}
    if (not isinstance(descriptor, dict)
            or set(descriptor) != {"kind", "relation", "scalarKind", "scalarFirst"}
            or descriptor["kind"] != "scalar-comparison"
            or not isinstance(descriptor["relation"], str) or not isinstance(descriptor["scalarKind"], str)
            or descriptor["relation"] not in relations or descriptor["scalarKind"] not in kinds
            or type(descriptor["scalarFirst"]) is not bool):
        raise RuntimeError("Invalid scalar comparison contract descriptor")
    relation, kind, first = descriptor["relation"], descriptor["scalarKind"], descriptor["scalarFirst"]
    width, scalar_type = kinds[kind]
    reference = {"type": "Nethermind.Int256.UInt256&", "IsIn": True, "IsOut": False}
    scalar = {"type": scalar_type, "IsIn": False, "IsOut": False}
    actual = {"isStatic": True, "returnType": "System.Boolean", "hasThis": False,
              "parameters": [scalar, reference] if first else [reference, scalar]}
    check_calling_convention(actual, entry["callingConvention"])
    expected = (f"System.Boolean Nethermind.Int256.UInt256::{relations[relation]}("
                + ",".join(p["type"] for p in actual["parameters"]) + ")")
    if entry["signature"] != expected:
        raise RuntimeError("Scalar comparison descriptor differs from selected operator")
    contract = (f"UInt256Model.Compare.ScalarContract {{program}} Extracted.entryIndex .{relation}\n"
                f"      initial input (.{kind} word) {str(first).lower()}")
    return typed_gate("UInt256.Methods.Compare.Automation",
        f"(initial : Bytes) (input : Nat) (word : {width})", "initial input word", contract,
        "scalar_comparison_execute initial, input", entry["verification"].get("allProfiles", False))


def bitwise_gate(entry):
    descriptor = entry["verification"]["template"]
    returning = descriptor.get("kind") == "returning-bitwise"
    operations = {"and", "or", "xor", "not"} if returning else {"and", "or", "xor"}
    if (set(descriptor) != {"kind", "operation"}
            or descriptor["kind"] not in {"binary-bitwise", "returning-bitwise"}
            or not isinstance(descriptor["operation"], str)
            or descriptor["operation"] not in operations
            or entry["verification"].get("allProfiles", False)):
        raise RuntimeError(f"Invalid {'returning' if returning else 'binary'} bitwise contract descriptor")
    operation = descriptor["operation"]
    parameters = [{"type": "Nethermind.Int256.UInt256&", "IsIn": True, "IsOut": False}] * (1 if operation == "not" else 2)
    result_type = "Nethermind.Int256.UInt256" if returning else "System.Void"
    if not returning:
        parameters += [{"type": "Nethermind.Int256.UInt256&", "IsIn": False, "IsOut": True}]
    check_calling_convention({"isStatic": True, "hasThis": False, "returnType": result_type,
                              "parameters": parameters}, entry["callingConvention"])
    operators = {"and": "op_BitwiseAnd", "or": "op_BitwiseOr", "xor": "op_ExclusiveOr", "not": "op_OnesComplement"}
    method = operators[operation] if returning else operation.title()
    expected = (f"{result_type} Nethermind.Int256.UInt256::{method}("
                + ",".join(p["type"] for p in parameters) + ")")
    if entry["signature"] != expected:
        raise RuntimeError("Binary bitwise descriptor differs from selected operation")
    if returning:
        unary = operation == "not"
        arguments = "initial input" if unary else "initial left right"
        contract = (f"UInt256Model.Bitwise.NotReturnContract {{program}} Extracted.entryIndex initial input" if unary
                    else f"UInt256Model.Bitwise.ReturnContract {{program}} Extracted.entryIndex .{operation}\n"
                         "      initial left right")
        execution = ("not_bitwise_return_execute initial, input" if unary else
                     f"binary_bitwise_return_execute initial, left, right, UInt256Proof.Bitwise.value_{operation}")
        return typed_gate("UInt256.Methods.Bitwise.ReturnAutomation",
            "(initial : Bytes) (input : Nat)" if unary else "(initial : Bytes) (left right : Nat)",
            arguments, contract, execution, family=bool(entry["verification"].get("familyCoverage")))
    contract = (f"UInt256Model.Bitwise.Contract {{program}} Extracted.entryIndex .{operation}\n"
                "      initial left right out")
    return typed_gate("UInt256.Methods.Bitwise.Automation", "(initial : Bytes) (left right out : Nat)",
        "initial left right out", contract,
        f"binary_bitwise_execute initial, left, right, out, UInt256Proof.Bitwise.value_{operation}",
        family=bool(entry["verification"].get("familyCoverage")))


def scalar_equality_gate(entry):
    descriptor = entry["verification"]["template"]
    kinds = {"u32": ("W32", "System.UInt32"), "u64": ("W64", "System.UInt64"),
             "s32": ("W32", "System.Int32"), "s64": ("W64", "System.Int64")}
    if (set(descriptor) != {"kind", "scalarKind", "scalarFirst", "instance", "negateResult"}
            or descriptor["kind"] != "scalar-equality"
            or not isinstance(descriptor["scalarKind"], str) or descriptor["scalarKind"] not in kinds
            or any(type(descriptor[key]) is not bool for key in ("scalarFirst", "instance", "negateResult"))
            or entry["verification"].get("allProfiles", False)):
        raise RuntimeError("Invalid scalar equality contract descriptor")
    kind, first, instance, negate = (descriptor[key] for key in
                                   ("scalarKind", "scalarFirst", "instance", "negateResult"))
    if instance and (first or negate):
        raise RuntimeError("Instance equality descriptor differs from Equals")
    width, scalar_type = kinds[kind]
    reference = {"type": "Nethermind.Int256.UInt256&", "IsIn": True, "IsOut": False}
    scalar = {"type": scalar_type, "IsIn": False, "IsOut": False}
    parameters = [scalar] if instance else [scalar, reference] if first else [reference, scalar]
    check_calling_convention({"isStatic": not instance, "hasThis": instance,
                              "returnType": "System.Boolean", "parameters": parameters}, entry["callingConvention"])
    name = "Equals" if instance else "op_Inequality" if negate else "op_Equality"
    expected = (f"System.Boolean Nethermind.Int256.UInt256::{name}("
                + ",".join(parameter["type"] for parameter in parameters) + ")")
    if entry["signature"] != expected:
        raise RuntimeError("Scalar equality descriptor differs from selected API")
    contract = (f"UInt256Model.Equality.ScalarContract {{program}} Extracted.entryIndex\n"
                f"      initial input (.{kind} word) {str(first).lower()} {str(negate).lower()}")
    return typed_gate("UInt256.Methods.Equality.Automation",
        f"(initial : Bytes) (input : Nat) (word : {width})", "initial input word", contract,
        "scalar_equality_execute initial, input", family=bool(entry["verification"].get("familyCoverage")))


def audit_module(entry):
    if "template" not in entry["verification"]:
        return handwritten_gate(entry)
    descriptor = entry["verification"].get("template", {})
    if not isinstance(descriptor, dict):
        raise RuntimeError("Invalid typed audit descriptor")
    if not isinstance(descriptor.get("kind"), str):
        raise RuntimeError("Invalid typed audit template kind")
    if descriptor.get("kind") == "scalar-comparison":
        return scalar_comparison_gate(entry)
    if descriptor.get("kind") in {"binary-bitwise", "returning-bitwise"}:
        return bitwise_gate(entry)
    if descriptor.get("kind") == "scalar-equality":
        return scalar_equality_gate(entry)
    raise RuntimeError("Unsupported typed audit template")
