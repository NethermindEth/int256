import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow

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

#print axioms CallingConditions.after_preserving_inputs
end UInt256Model.Safety
