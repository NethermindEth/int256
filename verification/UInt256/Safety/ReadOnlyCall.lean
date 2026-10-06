import UInt256.Safety.PrivateCalls

namespace UInt256Model.Safety
open CIL.Safety

theorem CallingConditions.after_readonly_call {program : CIL.Program}
    {before after : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program before inputs outputs)
    {fuel method : Nat} {args values : List Value}
    (invoked : invoke program fuel method args before = .ok (after, values))
    (authority : AccessBelow before.nextIdentity before after)
    (preserved : ∀ id, id < before.nextIdentity → ∀ offset, after.cells id offset = before.cells id offset) :
    CallingConditions program after inputs outputs := by
  apply call.after_preserving_inputs
    (invoke_preserves_wellFormed _ _ _ _ _ _ _ call.1.1 invoked) authority
    (invoke_preserves_static_world _ _ _ _ _ _ _ call.1.1 call.2 invoked)
  intro reference member offset _
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  exact preserved reference.allocation (call.1.1.1 _ _ present).1 _

theorem CallingConditions.input_value_of_caller_eq {program : CIL.Program}
    {before after : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program before inputs outputs)
    (preserved : ∀ id, id < before.nextIdentity → ∀ offset, after.cells id offset = before.cells id offset)
    (input : Reference) (member : input ∈ inputs) : inputValue after input = inputValue before input := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  have bytes : (fun offset => (after.cells input.allocation offset).bits) =
      (fun offset => (before.cells input.allocation offset).bits) := by
    funext offset
    rw [preserved input.allocation (call.1.1.1 _ _ present).1 offset]
  simp only [inputValue, bytes]

#print axioms CallingConditions.after_readonly_call
#print axioms CallingConditions.input_value_of_caller_eq
end UInt256Model.Safety
