import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow
import CIL.Safety.MethodContract

namespace UInt256Model.Safety
open CIL.Safety

/-- Preserve ordinary caller requirements across a helper that retains input
    bytes and access authority. Private stores need not preserve all memory. -/
theorem CallingConditions.after_preserving_inputs {program : CIL.Program}
    {before after : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program before inputs outputs)
    (wellFormed : after.WellFormed) (authority : AccessBelow before.nextIdentity before after)
    (world : StaticWorldValid (programStaticDescriptors program) after)
    (bytes : ∀ reference ∈ inputs, ∀ offset, offset < 32 →
      after.cells reference.allocation (reference.offset + offset) =
        before.cells reference.allocation (reference.offset + offset)) :
    CallingConditions program after inputs outputs := by
  refine ⟨⟨wellFormed, ?_, ?_⟩, world⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed inputMember)
    exact ⟨_, authority.read_eq (call.input_snapshot inputMember) (call.1.1.1 _ _ present).1
      (bytes reference inputMember)⟩
  · intro view member
    have writable := call.1.2.2 view member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
    exact authority.access writable (call.1.1.1 _ _ present).1

/-- A call confined to two private words preserves caller input snapshots. -/
theorem private_input_bytes {program : CIL.Program} {first second : Reference}
    {before after : Memory} (framed : Confined [(first, 8), (second, 8)] before after)
    {inputs outputs : List Reference} (call : CallingConditions program before inputs outputs)
    {reference : Reference} (member : reference ∈ inputs)
    (notFirst : reference.allocation ≠ first.allocation)
    (notSecond : reference.allocation ≠ second.allocation) :
    (fun offset => (after.cells reference.allocation offset).bits) =
      (fun offset => (before.cells reference.allocation offset).bits) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  funext offset
  rw [framed.cells_apart (call.1.1.1 _ _ present).1 (by simp [notFirst, notSecond]) offset]

/-- Caller authority, readable inputs and static data survive a call confined to two private words. -/
theorem private_calling_conditions {program : CIL.Program} {first second : Reference}
    {before after : Memory} (framed : Confined [(first, 8), (second, 8)] before after)
    (formed : after.WellFormed)
    (world : StaticWorldPreserved program before after)
    {inputs outputs : List Reference} (call : CallingConditions program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ first.allocation ∧ reference.allocation ≠ second.allocation) :
    CallingConditions program after inputs outputs := by
  refine ⟨⟨formed, ?_, ?_⟩, world call.2⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨notFirst, notSecond⟩ := separate reference inputMember
    exact ⟨_, framed.read_apart call.1.1 (call.input_snapshot inputMember) (by simp [Apart, wordView, notFirst, notSecond])⟩
  · intro view member
    have writable := call.1.2.2 view member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
    exact (framed.access_write _ (call.1.1.1 _ _ present).1 _ _).trans writable

#print axioms CallingConditions.after_preserving_inputs
#print axioms private_input_bytes
#print axioms private_calling_conditions
end UInt256Model.Safety
