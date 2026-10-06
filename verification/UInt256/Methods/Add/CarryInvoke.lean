import Extracted
import CIL.Safety.WordLocals
import UInt256.Methods.Add.CarryMemory
import CIL.Safety.ReturnMemory

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

namespace UInt256Proof.Safety

open CIL.Safety

/-- A total checked invocation from ordinary caller permissions, including
    setup, body and teardown. Caller carry/output overlap is permitted. -/
theorem carry_invoke_succeeds (a b c : BitVec 64) (carry output : Reference) (memory : Memory)
    (wellFormed : memory.WellFormed)
    (carryReadable : read memory carry 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carry 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ()) :
    ∃ fuel result,
      invoke Extracted.program fuel Extracted.addWithCarryIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
        memory = .ok (result, []) ∧
      loadValue result (.address output) 8 = .ok (.i64 (a + b + c)) ∧
      (WordsDisjoint carry output → loadValue result (.address carry) 8 = .ok (.i64 (carryWord a b c))) ∧
      (∀ id offset, id < memory.nextIdentity → OutsideWord carry id offset → OutsideWord output id offset →
        result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 8 1 = .ok (numberBytes (a + b + c).toNat 8) ∧
      (WordsDisjoint carry output → read result carry 8 1 = .ok (numberBytes (carryWord a b c).toNat 8)) := by
  let args := [Value.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
  have fc := access_reference_valid _ _ _ _ _ carryWritable
  have fo := access_reference_valid _ _ _ _ _ outputWritable
  obtain ⟨ca, cp, _, _⟩ := formed_reference_live _ _ _ fc
  obtain ⟨oa, op, _, _⟩ := formed_reference_live _ _ _ fo
  have carryOld := (wellFormed.1 _ _ cp).1
  have outputOld := (wellFormed.1 _ _ op).1
  obtain ⟨first, second, frame, enteredMemory, entered, locals, owned, distinct,
    _, _, firstWritable, secondWritable, preserved⟩ := carry_frame_setup memory args wellFormed
  have fresh := enterFrame_fresh _ _ _ _ _ entered
  have firstNew := (fresh.2 first.allocation (by rw [owned]; simp)).1
  have secondNew := (fresh.2 second.allocation (by rw [owned]; simp)).1
  have readCarry : read enteredMemory carry 8 1 = .ok (numberBytes c.toNat 8) := by
    rw [preserved.read carry carryOld 8 1]; exact carryReadable
  have writeCarry : access enteredMemory carry 8 1 true = .ok () := by
    rw [preserved.access carry carryOld 8 1 true]; exact carryWritable
  have writeOutput : access enteredMemory output 8 1 true = .ok () := by
    rw [preserved.access output outputOld 8 1 true]; exact outputWritable
  obtain ⟨stored, executed, outputRead, carryRead, footprint, retainedAccess⟩ := carry_body_succeeds a b c carry output first second
    frame enteredMemory locals distinct (Nat.ne_of_lt (Nat.lt_of_lt_of_le carryOld firstNew))
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le carryOld secondNew))
    firstWritable secondWritable readCarry writeCarry writeOutput
  have returned := leaveFrame_preserves_memory_below frame stored memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  have outputRead' : read (leaveFrame frame stored) output 8 1 = .ok (numberBytes (a + b + c).toNat 8) := by
    rw [returned.read output outputOld 8 1]; exact outputRead
  refine ⟨Extracted.addWithCarryBody.code.length + 1, leaveFrame frame stored, ?_,
    load_word64_of_read outputRead', ?_, ?_, ?_, outputRead', ?_⟩
  · have checked : args.mapM (checkedValue memory) = .ok args := by
      simp [args, checkedValue, numericValue, formValue, fc, fo, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp only [cil_code] at entered
    change invoke Extracted.program _ Extracted.addWithCarryIndex args memory = _
    simpa only [invoke, cil_code, checked, entered, Except.mapError, Bind.bind, Except.bind] using executed

  · intro disjoint
    apply load_word64_of_read
    rw [returned.read carry carryOld 8 1]
    exact carryRead disjoint
  · intro id offset old outsideCarry outsideOutput
    rw [returned.cells id old offset,
      footprint id offset (Nat.ne_of_lt (Nat.lt_of_lt_of_le old firstNew))
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le old secondNew)) outsideCarry outsideOutput,
      preserved.cells id old offset]

  · exact preserved.accessBelow.trans
      ((retainedAccess.weaken fresh.1.next).trans returned.accessBelow)

  · intro disjoint
    rw [returned.read carry carryOld 8 1]
    exact carryRead disjoint

#print axioms carry_invoke_succeeds

end UInt256Proof.Safety
