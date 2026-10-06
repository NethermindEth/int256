import UInt256.Methods.Add.SmallSetup
import UInt256.Methods.Add.SmallPrefix
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- A private word store retains the original caller snapshot and all existing
    frame access authority. It can be repeated for each operand limb. -/
theorem small_private_store (original entered current : CIL.Safety.Memory)
    (input output : Reference) (word value : BitVec 64) (frame : Frame) (slots tailSlots)
    (call : CallingConditions Extracted.program original [input] [output])
    (currentCall : CallingConditions Extracted.program current [input] [output])
    (enteredWF : entered.WellFormed)
    (layout : frame.locals = slots ++ tailSlots)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs slots)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (initial : BitVec 64)
    (specified : smallWordSpecs[index]? = some (some initial)) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes .word64 reference) ∧
      read after reference 8 1 = .ok (numberBytes value.toNat 8) ∧
      MemoryBelow original.nextIdentity original after ∧
      CallingConditions Extracted.program after [input] [output] ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes value.toNat 8) 1 = .ok after ∧
      ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal index) pc
        (smallArguments input output word) frame (.scalar (.i64 value) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := small_word_local layout homes index initial specified
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have old := (enteredWF.1 reference.allocation allocation ready.present).1
  have permitted := authority.access writable old
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 value permitted
  have caller := preserved.trans (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have afterWF := write_preserves_wellFormed _ _ _ _ _ currentCall.1.1 written
  have afterWorld := write_preserves_static_world _ _ _ _ _ _ currentCall.2 written
  refine ⟨reference, after, slot, loaded, caller,
    call.after_memory_below caller afterWF afterWorld,
    authority.trans (write_preserves_access_below written _), written, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := Extracted.addScalarUInt64Body) (pc := pc)
    (args := smallArguments input output word) (rest := rest) value slot permitted
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

#print axioms small_private_store

end UInt256Proof.Safety
