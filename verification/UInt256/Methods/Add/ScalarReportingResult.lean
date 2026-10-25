import UInt256.Safety.Calling
import UInt256.Safety.OutputAccess
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Common arithmetic and memory guarantees, also used when retiring the public frame. -/
structure ARMScalarPost (original final : Memory) (returned : List Value)
    (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original left + inputValue original right
  scalar : ∃ flag : BitVec 32, returned = [.scalar (.i32 flag)]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Reporting adds the exact initial-input overflow bit when requested. -/
structure ARMScalarReportingPost (original final : Memory) (returned : List Value)
    (left right output : Reference) (flag : BitVec 32)
    extends ARMScalarPost original final returned left right output where
  overflow : flag ≠ BitVec.ofNat 32 0 → returned = [.scalar (.i32
    (if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0))]

/-- Retire the parent after either certified child while retaining original
    caller arithmetic and bytes. Only private owned allocations are expired. -/
theorem arm_scalar_retire {program : CIL.Program} (original current final : Memory) (frame : Frame)
    (left right output : Reference) (returned : List Value)
    (call : CallingConditions program original [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (wellFormed : final.WellFormed)
    (value : inputValue final output = inputValue original left + inputValue original right)
    (scalar : ∃ flag : BitVec 32, returned = [.scalar (.i32 flag)])
    (writable : access final output 32 1 true = .ok ())
    (footprint : ∀ id, id < current.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = current.cells id offset) :
    ARMScalarPost original (leaveFrame frame final) returned left right output := by
  have retired := leaveFrame_preserves_memory_below frame final original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame final).cells output.allocation offset).bits) =
      (fun offset => (final.cells output.allocation offset).bits) := by
    funext offset
    rw [retired.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ wellFormed, ?_, scalar,
    (retired.access output outputOld 32 1 true).trans writable, ?_⟩
  · simpa only [inputValue, bytes] using value
  · intro id old offset untouched
    exact (retired.cells id old offset).trans
      ((footprint id (Nat.lt_of_lt_of_le old next) offset untouched).trans (preserved.cells id old offset))


#print axioms arm_scalar_retire
end UInt256Proof.Add.Safety
