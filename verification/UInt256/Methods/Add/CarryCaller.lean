import UInt256.Methods.Add.CarryContract
import UInt256.Safety.CallerSetup

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- A carry helper writing private homes preserves caller input snapshots.
    Input views may still overlap one another or the caller's output freely. -/
theorem CarryPost.private_input_bytes {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions Extracted.program before inputs outputs)
    {reference : Reference} (member : reference ∈ inputs)
    (notCarry : reference.allocation ≠ carryRef.allocation)
    (notOutput : reference.allocation ≠ output.allocation) :
    (fun offset => (after.cells reference.allocation offset).bits) =
      (fun offset => (before.cells reference.allocation offset).bits) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  have old := (call.1.1.1 _ _ present).1
  funext offset
  rw [post.footprint _ _ old (Or.inl notCarry) (Or.inl notOutput)]

/-- Retain read/write authority, original readable input bytes and static data
    across the actual helper invocation. Exact permission equality is not needed. -/
theorem CarryPost.private_calling_conditions {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions Extracted.program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ carryRef.allocation ∧ reference.allocation ≠ output.allocation) :
    CallingConditions Extracted.program after inputs outputs := by
  refine ⟨⟨post.wellFormed, ?_, ?_⟩, post.staticWorld call.2⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed inputMember)
    have old := (call.1.1.1 _ _ present).1
    obtain ⟨notCarry, notOutput⟩ := separate reference inputMember
    refine ⟨_, post.access.read_eq (call.input_snapshot inputMember) old ?_⟩
    intro i _
    exact post.footprint _ _ old (Or.inl notCarry) (Or.inl notOutput)
  · intro view member
    have writable := call.1.2.2 view member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
    exact post.access.access writable (call.1.1.1 _ _ present).1

theorem CarryPost.private_input_field {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions Extracted.program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ carryRef.allocation ∧ reference.allocation ≠ output.allocation)
    {reference : Reference} (member : reference ∈ inputs) (index : Fin 4) (rest : List Value) :
    instruction (.field index) (.reference (.address reference) :: rest) after =
      .ok (after, .scalar (.i64 (inputLimb before reference index)) :: rest) := by
  rw [(post.private_calling_conditions call separate).input_field_instruction member index rest]
  simp only [inputLimb, post.private_input_bytes call member (separate reference member).1
    (separate reference member).2]

#print axioms CarryPost.private_input_bytes
#print axioms CarryPost.private_calling_conditions
#print axioms CarryPost.private_input_field

end UInt256Proof.Safety
