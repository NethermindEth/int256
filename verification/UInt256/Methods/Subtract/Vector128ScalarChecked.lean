import UInt256.Methods.Subtract.Vector128ParentCall
import CIL.Safety.ReturnMemory
import UInt256.Methods.Subtract.ScalarSmallChecked

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Bridge the child result back to the original inputs and retire only the
    parent's private allocations. -/
theorem vector128_scalar_finish (original current : Memory) (frame : Frame)
    (left right output : Reference) (upper : BitVec 64) (large : upper ≠ BitVec.ofNat 64 0)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex scalarFirstDecision (binaryArguments left right output)
        frame [.scalar (.i64 upper)] current = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let post := fun final returned => SubtractResult original final returned left right output
  apply vector128_parent_call current left right output upper large frame currentCall post
  intro childFuel final certified result writable footprint
  have wellFormed := invoke_preserves_wellFormed _ _ _ _ _ _ _ currentCall.1.1 certified.1
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  have retired := leaveFrame_preserves_memory_below frame final original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame final).cells output.allocation offset).bits) =
      (fun offset => (final.cells output.allocation offset).bits) := by
    funext offset
    rw [retired.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ wellFormed, ?_, ?_,
    (retired.access output outputOld 32 1 true).trans writable, ?_⟩
  · rw [keptLeft, keptRight] at result
    simpa only [inputValue, bytes] using result
  · simp only [subtractUnderflow, keptLeft, keptRight]
  · intro id old offset untouched
    exact (retired.cells id old offset).trans
      ((footprint id offset (Nat.lt_of_lt_of_le old next) untouched).trans (preserved.cells id old offset))

#print axioms vector128_scalar_finish
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

theorem vector128_scalar_large (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (large : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final returned,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, returned) ∧ SubtractResult memory final returned left right output := by
  let args := binaryArguments left right output
  let post := fun final returned => SubtractResult memory final returned left right output
  obtain ⟨frame, entered, setup, homes, _, enteredWF⟩ := scalar_frame_setup memory args call.1.1
  have executed := scalar_right_prefix_checked memory entered left right output frame call setup homes post (by
    intro home current slot loaded preserved currentCall authority
    exact vector128_scalar_finish memory current frame left right output _ large call currentCall preserved
      (scalar_private_next memory entered current frame homes enteredWF currentCall.1.1 authority)
      (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1))
  obtain ⟨fuel, final, returned, finished, result⟩ := executed
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  dsimp only [args] at checked setup
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  exact ⟨fuel, final, returned,
    by simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished, result⟩

/-- Both small-operand and vector routes retain the exact reporting contract. -/
theorem vector128_scalar_checked (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final returned,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, returned) ∧ SubtractResult memory final returned left right output := by
  by_cases small : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 = BitVec.ofNat 64 0
  · exact scalar_right_small_checked memory left right output call small
  · exact vector128_scalar_large memory left right output call small

#print axioms vector128_scalar_large
#print axioms vector128_scalar_checked
end UInt256Proof.Subtract.Safety
