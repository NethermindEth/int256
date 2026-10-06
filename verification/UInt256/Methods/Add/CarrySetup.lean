import Extracted
import CIL.Safety.WordLocals

namespace UInt256Proof.Safety

open CIL.Safety

/-- The extracted carry helper's numeric homes are initialized, independently
    writable and private; setup preserves all earlier caller memory. -/
theorem carry_frame_setup (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ first second frame result,
      enterFrame Extracted.addWithCarryBody args memory = .ok (frame, result) ∧
      frame.locals = [.bytes .word64 first, .bytes .word64 second] ∧
      frame.owned = [first.allocation, second.allocation] ∧
      first.allocation ≠ second.allocation ∧
      read result first 8 1 = .ok (numberBytes 0 8) ∧
      read result second 8 1 = .ok (numberBytes 0 8) ∧
      access result first 8 1 true = .ok () ∧
      access result second 8 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨first, middle, madeFirst, readFirst, writeFirst, _⟩ :=
    make_local_word64 memory memory.nextIdentity (BitVec.ofNat 64 0) wellFormed
  have wfMiddle := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed madeFirst
  obtain ⟨second, result, madeSecond, readSecond, writeSecond, preserved⟩ :=
    make_local_word64 middle memory.nextIdentity (BitVec.ofNat 64 0) wfMiddle
  have freshFirst := (makeLocal_fresh _ _ _ _ _ _ _ madeFirst).2 first.allocation (by simp)
  have freshSecond := (makeLocal_fresh _ _ _ _ _ _ _ madeSecond).2 second.allocation (by simp)
  let frame : Frame := ⟨memory.nextIdentity, [.bytes .word64 first, .bytes .word64 second],
    [first.allocation, second.allocation], []⟩
  have entered : enterFrame Extracted.addWithCarryBody args memory = .ok (frame, result) := by
    simp [enterFrame, cil_code, makeLocals, madeFirst, madeSecond, makeArgumentHomes,
      frame, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨first, second, frame, result, entered, rfl, rfl, ?_, ?_, readSecond, ?_, writeSecond,
    enterFrame_preserves_caller_memory _ _ _ _ _ entered⟩
  · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le freshFirst.2 freshSecond.1)
  · rw [preserved.read first freshFirst.2 8 1]
    exact readFirst
  · rw [preserved.access first freshFirst.2 8 1 true]
    exact writeFirst

#print axioms carry_frame_setup

end UInt256Proof.Safety
