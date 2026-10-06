import UInt256.Methods.Equality.PrimitiveSafetyPrefix

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem primitive_setup (memory : Memory) (left : Reference) (right : CIL.Value)
    (call : CallingConditions Extracted.program memory [left] []) :
    ∃ frame entered home,
      enterFrame primitiveBody (primitiveArguments left right) memory = .ok (frame, entered) ∧
      frame.locals = [.bytes .vector256 home] ∧
      access entered home 32 1 true = .ok () ∧
      home.allocation = memory.nextIdentity ∧
      CallingConditions Extracted.program entered [left] [] ∧
      inputValue entered left = inputValue memory left := by
  obtain ⟨home, allocated, entered, allocation, _, stored, _, writable, _⟩ :=
    allocate_initialized256 memory memory.nextIdentity (BitVec.ofNat 256 0) call.1.1
  let frame : Frame := {
    activation := memory.nextIdentity, locals := [.bytes .vector256 home],
    owned := [home.allocation], arguments := [] }
  have setup : enterFrame primitiveBody (primitiveArguments left right) memory = .ok (frame, entered) := by
    conv in primitiveBody => cbv
    simp [enterFrame, makeLocals, makeLocal, localWidth, allocation, stored,
      makeArgumentHomes, frame, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨frame, entered, home, setup, rfl, writable,
    (allocateHome_fresh _ _ _ _ _ allocation).2.1,
    call.after_frame_setup setup, call.input_value_after_setup setup (by simp)⟩

#print axioms primitive_setup

end UInt256Proof.Equality.Safety
