import UInt256.Methods.Subtract.VectorSafetyFast

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Saved state immediately before the first output write. Values refer to the
    initial caller snapshot, not to potentially aliased output storage. -/
structure VectorPrepared (original current : Memory) (left right : Reference) (frame : Frame) where
  leftHome : Reference
  rightHome : Reference
  differenceHome : Reference
  maskHome : Reference
  incomingHome : Reference
  leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome)
  rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome)
  differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome)
  maskSlot : frame.locals[3]? = some (.bytes .vector256 maskHome)
  incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome)
  leftRead : read current leftHome 32 1 = .ok (numberBytes (inputValue original left).toNat 32)
  rightRead : read current rightHome 32 1 = .ok (numberBytes (inputValue original right).toNat 32)
  differenceRead : read current differenceHome 32 1 = .ok (numberBytes
    (CIL.Vector.zip256 (· - ·) (inputValue original left) (inputValue original right)).toNat 32)
  maskRead : read current maskHome 32 1 = .ok (numberBytes
    (generatedBorrow (inputValue original left) (inputValue original right)).toNat 32)
  incomingRead : read current incomingHome 32 1 = .ok (numberBytes
    (incomingBorrow (generatedBorrow (inputValue original left) (inputValue original right))).toNat 32)

theorem vector_prepare_checked (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArgument : args[0]? = some (.reference (.address left)))
    (rightArgument : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, VectorPrepared original after left right frame →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex vectorOutputStart args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredWF := (call.after_frame_setup setup).1.1
  apply vector_operand_dispatch entered frame args post
  apply vector_operands_checked original entered inputs outputs left right frame args call setup homes
    leftMember rightMember leftArgument rightArgument post
  intro leftHome rightHome operands leftSlot rightSlot _ leftRead rightRead preserved currentCall authority operandNext
  apply vector_difference_checked original entered operands inputs outputs frame args call currentCall
    enteredWF homes preserved authority leftHome rightHome (inputValue original left) (inputValue original right)
    leftSlot rightSlot leftRead rightRead post
  intro differenceHome differences differenceSlot differenceRead leftRead rightRead preserved currentCall authority differenceNext
  apply vector_borrow_dispatch differences frame args post
  apply vector_borrows_checked original entered differences inputs outputs frame args call currentCall
    enteredWF homes preserved authority leftHome rightHome differenceHome (inputValue original left) (inputValue original right)
    leftSlot rightSlot leftRead rightRead differenceSlot differenceRead post
  intro maskHome incomingHome after maskSlot incomingSlot maskRead incomingRead earlier retained afterCall afterAuthority borrowNext
  have leftOld := homes.ordered 0 3 .vector256 .vector256 leftHome maskHome (by decide) leftSlot maskSlot
  have rightOld := homes.ordered 1 3 .vector256 .vector256 rightHome maskHome (by decide) rightSlot maskSlot
  have differenceOld := homes.ordered 2 3 .vector256 .vector256 differenceHome maskHome
    (by decide) differenceSlot maskSlot
  exact continuation after ⟨leftHome, rightHome, differenceHome, maskHome, incomingHome,
    leftSlot, rightSlot, differenceSlot, maskSlot, incomingSlot,
    (earlier.read leftHome leftOld 32 1).trans leftRead,
    (earlier.read rightHome rightOld 32 1).trans rightRead,
    (earlier.read differenceHome differenceOld 32 1).trans differenceRead, maskRead, incomingRead⟩
    retained afterCall afterAuthority (Nat.le_trans operandNext (Nat.le_trans differenceNext borrowNext))

#print axioms vector_prepare_checked

/-- Complete fast execution from the extracted vector method's first instruction.
    Both arithmetic and footprint refer to the initial caller memory. -/
theorem vector_fast_execution (original entered : Memory) (left right output : Reference)
    (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame vectorBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (fast : equalLanes (inputValue original left) (inputValue original right) &&&
      incomingBorrow (generatedBorrow (inputValue original left) (inputValue original right)) = 0) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (final, [.scalar (.i32 (if (inputValue original left).toNat < (inputValue original right).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (inputValue original left - inputValue original right).toNat 32) ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  have leftValue : UInt256Model.value (inputLimb original left) = inputValue original left :=
    UInt256Proof.input_value (fun offset => (original.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb original right) = inputValue original right :=
    UInt256Proof.input_value (fun offset => (original.cells right.allocation offset).bits) right.offset
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (inputValue original left).toNat < (inputValue original right).toNat then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (inputValue original left - inputValue original right).toNat 32) ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = original.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply vector_prepare_checked original entered [left, right] [output] left right frame
      (binaryArguments left right output) call setup homes (by simp) (by simp) rfl rfl post
    intro current saved preserved currentCall authority _
    obtain ⟨fuel, final, executed, result, footprint⟩ := vector_fast_output original entered current
      [left, right] [output] output frame (binaryArguments left right output) call currentCall (by simp)
      setup (call.after_frame_setup setup).1.1 homes authority rfl
      saved.leftHome saved.rightHome saved.differenceHome saved.maskHome saved.incomingHome
      (inputLimb original left) (inputLimb original right)
      saved.leftSlot saved.rightSlot saved.differenceSlot saved.maskSlot saved.incomingSlot
      (by simpa only [leftValue] using saved.leftRead)
      (by simpa only [rightValue] using saved.rightRead)
      (by simpa only [leftValue, rightValue] using saved.differenceRead)
      (by simpa only [leftValue, rightValue] using saved.maskRead)
      (by simpa only [leftValue, rightValue] using saved.incomingRead)
      (by simpa only [leftValue, rightValue] using fast)
    simp only [leftValue, rightValue] at executed result
    refine ⟨fuel, final, _, executed, rfl, result, ?_⟩
    intro id offset old outside
    exact (footprint id offset old outside).trans (preserved.cells id old offset)
  obtain ⟨fuel, final, returned, executed, flag, result, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, footprint⟩

#print axioms vector_fast_execution
end UInt256Proof.Subtract.Safety
