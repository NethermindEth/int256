import Extracted
import CIL.Safety.WordFrameSetup
import CIL.Safety.WordFootprint
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety

def smallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

def smallWordSpecs : List (Option (BitVec 64)) :=
  Extracted.subtractScalarUInt64Body.locals.map fun value => match value with
    | .i64 word => some word | _ => none

theorem small_frame_setup (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame result,
      enterFrame Extracted.subtractScalarUInt64Body args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity smallWordSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  word_frame_setup Extracted.subtractScalarUInt64Body smallWordSpecs (by rfl) (by rfl)
    (by rfl) memory args wf

#print axioms small_frame_setup

/-- A private word store retains the original caller snapshot and all existing
    frame access authority. It can be repeated for each operand limb. -/
theorem small_private_store (original entered current : CIL.Safety.Memory)
    (input output : Reference) (word value : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program original [input] [output])
    (currentCall : CallingConditions Extracted.program current [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs frame.locals)
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
      ∀ pc rest, step Extracted.subtractScalarUInt64Body (.setLocal index) pc
        (smallArguments input output word) frame (.scalar (.i64 value) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.word_at index initial specified
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
    (body := Extracted.subtractScalarUInt64Body) (pc := pc)
    (args := smallArguments input output word) (rest := rest) value slot permitted
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

#print axioms small_private_store

end UInt256Proof.Subtract.Safety
