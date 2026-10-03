"""Typed audit modules from explicit, source-hashed public contract descriptors."""

from methods import check_calling_convention


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
    all_profiles = ""
    if entry["verification"].get("allProfiles", False):
        all_profiles = f'''
theorem checked_all_profiles_contract : ∀ (profile : FeatureProfile), profile.Valid →
    ∀ (initial : Bytes) (input : Nat) (word : {width}),
    {contract.format(program="(reprofile Extracted.program profile)")} := by
  intro profile valid
  apply checked_profile_contract profile valid
  exact Program.profile_independent_agreement Extracted.program (by decide) _ _

#print axioms checked_all_profiles_contract
'''
    return f'''import UInt256.Methods.Compare.Automation

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Selected

theorem checked_contract : ∀ (initial : Bytes) (input : Nat) (word : {width}),
    {contract.format(program="Extracted.program")} := by
  intro initial input word
  scalar_comparison_execute initial, input

theorem checked_profile_contract : ∀ (profile : FeatureProfile), profile.Valid →
    Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ (initial : Bytes) (input : Nat) (word : {width}),
    {contract.format(program="(reprofile Extracted.program profile)")} := by
  intro profile _ agreement initial input word
  obtain ⟨fuel, final, execution, bytes⟩ := checked_contract initial input word
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← invoke_uniform_reprofile_eq Extracted.program Extracted.profile profile
    (uniform_of_profile_map _ _ Extracted.programProfiles) agreement]
  exact execution

#print axioms checked_contract
#print axioms checked_profile_contract
{all_profiles}
end UInt256Proof.Selected
'''


def binary_bitwise_gate(entry):
    descriptor = entry["verification"]["template"]
    if (set(descriptor) != {"kind", "operation"} or descriptor["kind"] != "binary-bitwise"
            or not isinstance(descriptor["operation"], str)
            or descriptor["operation"] not in {"and", "or", "xor"}
            or entry["verification"].get("allProfiles", False)):
        raise RuntimeError("Invalid binary bitwise contract descriptor")
    operation = descriptor["operation"]
    parameters = [{"type": "Nethermind.Int256.UInt256&", "IsIn": True, "IsOut": False}] * 2
    parameters += [{"type": "Nethermind.Int256.UInt256&", "IsIn": False, "IsOut": True}]
    check_calling_convention({"isStatic": True, "hasThis": False, "returnType": "System.Void",
                              "parameters": parameters}, entry["callingConvention"])
    expected = (f"System.Void Nethermind.Int256.UInt256::{operation.title()}("
                + ",".join(p["type"] for p in parameters) + ")")
    if entry["signature"] != expected:
        raise RuntimeError("Binary bitwise descriptor differs from selected operation")
    return f'''import UInt256.Methods.Bitwise.Automation

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Selected

theorem checked_contract : ∀ (initial : Bytes) (left right out : Nat),
    UInt256Model.Bitwise.Contract Extracted.program Extracted.entryIndex .{operation}
      initial left right out := by
  intro initial left right out
  binary_bitwise_execute initial, left, right, out, UInt256Proof.Bitwise.value_{operation}

theorem checked_profile_contract : ∀ (profile : FeatureProfile), profile.Valid →
    Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ (initial : Bytes) (left right out : Nat),
    UInt256Model.Bitwise.Contract (reprofile Extracted.program profile)
      Extracted.entryIndex .{operation} initial left right out := by
  intro profile _ agreement initial left right out
  obtain ⟨fuel, final, execution, bytes⟩ := checked_contract initial left right out
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← invoke_uniform_reprofile_eq Extracted.program Extracted.profile profile
    (uniform_of_profile_map _ _ Extracted.programProfiles) agreement]
  exact execution

#print axioms checked_contract
#print axioms checked_profile_contract
end UInt256Proof.Selected
'''


def audit_module(entry):
    descriptor = entry["verification"].get("template", {})
    if not isinstance(descriptor, dict):
        raise RuntimeError("Invalid typed audit descriptor")
    if descriptor.get("kind") == "scalar-comparison":
        return scalar_comparison_gate(entry)
    if descriptor.get("kind") == "binary-bitwise":
        return binary_bitwise_gate(entry)
    raise RuntimeError("Unsupported typed audit template")
