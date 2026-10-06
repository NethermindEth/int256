import UInt256.Methods.Add.Vector128SSEParentCall
import UInt256.Methods.Add.ScalarReportingResult

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- The vector route yields the same wrapping postcondition after parent retirement. -/
theorem sse_scalar_vector_finish
    (original current : Memory) (frame : Frame) (left right output : Reference) (flag : BitVec 32)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 75 ((binaryArguments left right output ++ [.scalar (.i32 flag)]))
        frame [] current = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  apply vector128_sse_parent_call current left right output flag frame currentCall post
  intro childFuel final returnedFlag certified result overflow writable footprint
  have wellFormed := invoke_preserves_wellFormed _ _ _ _ _ _ _ currentCall.1.1 certified.1
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  rw [keptLeft, keptRight] at result
  refine ⟨arm_scalar_retire original current final frame left right output [.scalar (.i32 returnedFlag)]
    call preserved next owned wellFormed result ⟨returnedFlag, rfl⟩ writable
    (fun id old offset untouched => footprint id offset old untouched), ?_⟩
  intro reporting
  have exactFlag := overflow reporting
  simp only [UInt256Proof.Safety.addOverflow, keptLeft, keptRight] at exactFlag
  rw [exactFlag]

#print axioms sse_scalar_vector_finish
end UInt256Proof.Add.Safety
