import CIL.Safety.MethodContract
import UInt256.Safety.CallerSetup

namespace UInt256Proof
open CIL.Safety UInt256Model.Safety

/-- A byte outside two words is outside their two-entry contract footprint. -/
theorem outside_words {first second : Reference} {id offset : Nat}
    (outFirst : OutsideWord first id offset) (outSecond : OutsideWord second id offset) :
    Outside [(first, 8), (second, 8)] id offset := by
  intro entry member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact outFirst
  · exact outSecond

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
  have old := (call.1.1.1 _ _ present).1
  funext offset
  rw [framed.cells _ old _ (outside_words (Or.inl notFirst) (Or.inl notSecond))]

/-- Caller authority, readable inputs and static data survive a call confined to two private words. -/
theorem private_calling_conditions {program : CIL.Program} {first second : Reference}
    {before after : Memory} (framed : Confined [(first, 8), (second, 8)] before after)
    (formed : after.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) before →
      StaticWorldValid (programStaticDescriptors program) after)
    {inputs outputs : List Reference} (call : CallingConditions program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ first.allocation ∧ reference.allocation ≠ second.allocation) :
    CallingConditions program after inputs outputs := by
  refine ⟨⟨formed, ?_, ?_⟩, world call.2⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed inputMember)
    have old := (call.1.1.1 _ _ present).1
    obtain ⟨notFirst, notSecond⟩ := separate reference inputMember
    refine ⟨_, (framed.read_eq _ old _ _ fun _ _ => outside_words (Or.inl notFirst) (Or.inl notSecond)).trans
      (call.input_snapshot inputMember)⟩
  · intro view member
    have writable := call.1.2.2 view member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
    exact (framed.access_write _ (call.1.1.1 _ _ present).1 _ _).trans writable

#print axioms outside_words
#print axioms private_input_bytes
#print axioms private_calling_conditions
end UInt256Proof
