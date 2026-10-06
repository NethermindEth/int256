import UInt256.Safety.OutputAccess
import CIL.Safety.ReturnMemory

namespace UInt256Model.Safety
open CIL.Safety

structure OutputResult (original final : Memory) (output : Reference)
    (expected : BitVec 256) (returned : List Value) : Prop where
  returns : returned = []
  wellFormed : final.WellFormed
  value : inputValue final output = expected
  writable : access final output 32 1 true = .ok ()
  readable : ∃ bytes, read final output 32 1 = .ok bytes
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Retiring private homes preserves the caller output, its initialized value,
    access authority, and all other original caller bytes. -/
theorem output_result_of_storage {program : CIL.Program} (original current result : Memory)
    (inputs : List Reference) (output : Reference) (expected : BitVec 256) (frame : Frame)
    (originalCall : CallingConditions program original inputs [output])
    (valid : CallingConditions program result inputs [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (caller : ∀ id, id < original.nextIdentity → ∀ offset, current.cells id offset = original.cells id offset)
    (value : inputValue result output = expected)
    (readable : ∃ bytes, read result output 32 1 = .ok bytes)
    (outside : ∀ id offset, OutsideOutput output id offset → result.cells id offset = current.cells id offset) :
    OutputResult original (leaveFrame frame result) output expected [] := by
  have retained := leaveFrame_preserves_memory_below frame result original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (originalCall.output_formed (by simp : output ∈ [output]))
  have old := (originalCall.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame result).cells output.allocation offset).bits) =
      (fun offset => (result.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation old offset]
  refine ⟨rfl, leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_,
    (retained.access output old 32 1 true).trans (valid.1.2.2 (wordView output) (by simp)), ?_, ?_⟩
  · simpa only [inputValue, bytes] using value
  · obtain ⟨snapshot, loaded⟩ := readable
    exact ⟨snapshot, (retained.read output old 32 1).trans loaded⟩
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (caller id old offset))

#print axioms output_result_of_storage
end UInt256Model.Safety
