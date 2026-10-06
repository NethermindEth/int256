import UInt256.Methods.Subtract.VectorSafetyOutputExecution

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete checked vector execution from entry for both propagation branches.
    All arithmetic and caller-byte guarantees refer to the initial memory. -/
theorem vector_execution (original entered : Memory) (left right output : Reference)
    (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame vectorBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (final, [.scalar (.i32 (if (inputValue original left).toNat < (inputValue original right).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (inputValue original left - inputValue original right).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  have leftValue : UInt256Model.value (inputLimb original left) = inputValue original left :=
    UInt256Proof.input_value (fun offset => (original.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb original right) = inputValue original right :=
    UInt256Proof.input_value (fun offset => (original.cells right.allocation offset).bits) right.offset
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (inputValue original left).toNat < (inputValue original right).toNat then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (inputValue original left - inputValue original right).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = original.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply vector_prepare_checked original entered [left, right] [output] left right frame
      (binaryArguments left right output) call setup homes (by simp) (by simp) rfl rfl post
    intro current saved preserved currentCall authority advanced
    obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_output_execution original entered current
      [left, right] [output] output frame (binaryArguments left right output) call currentCall (by simp)
      setup (call.after_frame_setup setup).1.1 advanced homes authority rfl
      saved.leftHome saved.rightHome saved.differenceHome saved.maskHome saved.incomingHome
      (inputLimb original left) (inputLimb original right)
      saved.leftSlot saved.rightSlot saved.differenceSlot saved.maskSlot saved.incomingSlot
      (by simpa only [leftValue] using saved.leftRead)
      (by simpa only [rightValue] using saved.rightRead)
      (by simpa only [leftValue, rightValue] using saved.differenceRead)
      (by simpa only [leftValue, rightValue] using saved.maskRead)
      (by simpa only [leftValue, rightValue] using saved.incomingRead)
    simp only [leftValue, rightValue] at executed result
    refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
    intro id offset old outside
    exact (footprint id offset old outside).trans (preserved.cells id old offset)
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩


#print axioms vector_execution
end UInt256Proof.Subtract.Safety
