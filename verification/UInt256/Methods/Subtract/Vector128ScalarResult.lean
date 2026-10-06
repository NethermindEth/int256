import UInt256.Methods.Subtract.Vector128ParentCall
import CIL.Safety.ReturnMemory

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
