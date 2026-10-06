import UInt256.Safety.PrivateWords
import UInt256.Safety.OutputReturn

namespace UInt256Model.Safety
open CIL.Safety

/-- A checked child result can be returned through its caller's private frame.
    The child footprint is composed with the prefix's original-byte guarantee. -/
theorem PrivateWords.finish_output {program : CIL.Program} {original entered current final : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs [output] frame known)
    (originalCall : CallingConditions program original inputs [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (expected : BitVec 256) (result : OutputResult current final output expected []) :
    OutputResult original (leaveFrame frame final) output expected [] := by
  have retained := leaveFrame_preserves_memory_below frame final original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (originalCall.output_formed (by simp : output ∈ [output]))
  have old := (originalCall.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame final).cells output.allocation offset).bits) =
      (fun offset => (final.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation old offset]
  refine ⟨rfl, leaveFrame_preserves_wellFormed _ _ result.wellFormed, ?_,
    (retained.access output old 32 1 true).trans result.writable, ?_, ?_⟩
  · simpa only [inputValue, bytes] using result.value
  · obtain ⟨snapshot, loaded⟩ := result.readable
    exact ⟨snapshot, (retained.read output old 32 1).trans loaded⟩
  · intro id bound offset outside
    exact (retained.cells id bound offset).trans
      ((result.footprint id (Nat.lt_of_lt_of_le bound (Nat.le_trans state.enteredBound state.next)) offset outside).trans
        (state.caller id bound offset))

#print axioms PrivateWords.finish_output
end UInt256Model.Safety
