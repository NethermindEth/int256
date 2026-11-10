import CIL.Safety.FrameMemoryBelow
import UInt256.Safety.LimbAccess

/-! Shared frame transport preserves UInt256 calling views and their initial input values. -/

namespace UInt256Model.Safety

open CIL.Safety

/-- Exact preservation of older caller storage transports the original call
    requirements across private allocation and local writes. -/
theorem CallingConditions.after_memory_below {program : CIL.Program}
    {memory updated : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs)
    (preserved : MemoryBelow memory.nextIdentity memory updated)
    (wellFormed : updated.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) updated) :
    CallingConditions program updated inputs outputs :=
  ⟨call.1.after_below preserved.accessBelow (Nat.le_refl _) wellFormed, world⟩

theorem CallingConditions.input_bytes_of_memory_below {program : CIL.Program}
    {memory updated : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs)
    (preserved : MemoryBelow memory.nextIdentity memory updated)
    {reference : Reference} (member : reference ∈ inputs) :
    (fun offset => (updated.cells reference.allocation offset).bits) =
      (fun offset => (memory.cells reference.allocation offset).bits) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  funext offset
  rw [preserved.cells reference.allocation (call.1.1.1 _ _ present).1 offset]

#print axioms CallingConditions.after_memory_below
#print axioms CallingConditions.input_bytes_of_memory_below

theorem CallingConditions.after_frame_setup {program : CIL.Program}
    {memory entered : CIL.Safety.Memory} {inputs outputs : List Reference}
    {body : CIL.Method} {args : List CIL.Safety.Value} {frame : Frame}
    (call : CallingConditions program memory inputs outputs)
    (setup : enterFrame body args memory = .ok (frame, entered)) :
    CallingConditions program entered inputs outputs :=
  ⟨call.1.after_enterFrame setup,
    enterFrame_preserves_static_world _ _ _ _ _ _ call.1.wellFormed call.2 setup⟩

theorem CallingConditions.input_bytes_after_setup {program : CIL.Program}
    {memory entered : CIL.Safety.Memory} {inputs outputs : List Reference}
    {body : CIL.Method} {args : List CIL.Safety.Value} {frame : Frame}
    (call : CallingConditions program memory inputs outputs)
    (setup : enterFrame body args memory = .ok (frame, entered))
    {reference : Reference} (member : reference ∈ inputs) :
    (fun offset => (entered.cells reference.allocation offset).bits) =
      (fun offset => (memory.cells reference.allocation offset).bits) :=
  call.input_bytes_of_memory_below (enterFrame_preserves_caller_memory _ _ _ _ _ setup) member

theorem CallingConditions.input_value_after_setup {program : CIL.Program}
    {memory entered : CIL.Safety.Memory} {inputs outputs : List Reference}
    {body : CIL.Method} {args : List CIL.Safety.Value} {frame : Frame}
    (call : CallingConditions program memory inputs outputs)
    (setup : enterFrame body args memory = .ok (frame, entered))
    {reference : Reference} (member : reference ∈ inputs) :
    inputValue entered reference = inputValue memory reference := by
  simp only [inputValue, call.input_bytes_after_setup setup member]

theorem CallingConditions.input_field_after_setup {program : CIL.Program}
    {memory entered : CIL.Safety.Memory} {inputs outputs : List Reference}
    {body : CIL.Method} {args : List CIL.Safety.Value} {frame : Frame}
    (call : CallingConditions program memory inputs outputs)
    (setup : enterFrame body args memory = .ok (frame, entered))
    {reference : Reference} (member : reference ∈ inputs) (index : Fin 4) (rest : List CIL.Safety.Value) :
    instruction (.fieldAt (8 * index.val) 8) (.reference (.address reference) :: rest) entered =
      .ok (entered, .scalar (.i64 (inputLimb memory reference index)) :: rest) := by
  rw [(call.after_frame_setup setup).input_field_instruction member index rest]
  simp only [inputLimb, call.input_bytes_after_setup setup member]

#print axioms CallingConditions.after_frame_setup
#print axioms CallingConditions.input_value_after_setup
#print axioms CallingConditions.input_field_after_setup

end UInt256Model.Safety
