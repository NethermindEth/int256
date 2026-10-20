import CIL.Safety.WordLocals
import CIL.Safety.WordFootprint
import CIL.Safety.StepComposition
import CIL.Safety.CallComposition
import CIL.Safety.AccessBelow
import CIL.Safety.ReturnMemory
import CIL.Safety.SymbolicExecution

namespace UInt256Proof.Add.CarrySafety
variable {program : CIL.Program} {index : Nat} {body : CIL.Method}

open CIL.Safety

/-- Frame metadata `enterFrame` reads; any other shape fails these equalities. -/
structure CarryShape (body : CIL.Method) : Prop where
  localKinds : body.localKinds = [.word64, .word64]
  locals : body.locals = [.i64 0, .i64 0]
  vectorArgs : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []

/-- Execution of a two-local carry body whose only memory effects are, in order,
    both local stores, the carry write `cw`, and the sum write. -/
def CarryRun (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (cw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ (a b c : BitVec 64) (carry output first second : Reference) (frame : Frame) (m0 m1 m2 m3 m4 : Memory),
    frame.locals = [.bytes .word64 first, .bytes .word64 second] →
    storeLocal m0 (.bytes .word64 first) (.scalar (.i64 (a + b))) = .ok (.bytes .word64 first, m1) →
    storeLocal m1 (.bytes .word64 second) (.scalar (.i64 (a + b + c))) = .ok (.bytes .word64 second, m2) →
    loadLocal m1 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))) →
    loadValue m1 (.address carry) 8 = .ok (.i64 c) →
    loadLocal m2 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))) →
    loadLocal m2 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))) →
    loadLocal m3 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))) →
    form m1 carry = .ok carry → form m2 carry = .ok carry → form m3 output = .ok output →
    write m2 carry (numberBytes (cw a b c).toNat 8) 1 = .ok m3 →
    write m3 output (numberBytes (a + b + c).toNat 8) 1 = .ok m4 →
    run program (body.code.length + 1) index 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
      frame [] m0 = .ok (leaveFrame frame m4, [])

set_option hygiene false in
/-- Prove `CarryRun` for an extracted body by executing every fetched instruction, including
    calls to frameless pure helpers; `normalize` puts the carry write in evaluated form. -/
macro "carry_run_steps " "[" normalize:term,* "]" : tactic => `(tactic| (
  intro a b c carry output first second frame m0 m1 m2 m3 m4 locals s0 s1 r0 rc r1 r2 r3 fc1 fc2 fo3 wc wo
  simp [$[$normalize:term],*] at wc
  simp [BitVec.toNat_add] at wo
  simp only [cil_code]
  repeat'
    first
    | apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, locals, s0, s1, r0, rc, r1, r2, r3,
              checkedValue, numericValue, formValue, fc1, fc2, fo3,
              pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary, instruction, storeValue,
              referenceAt, wc, wo, checkedAt, Except.mapError,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact ⟨rfl, rfl, rfl, rfl⟩
    | apply run_call_of_invoke
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp [cil_code, step, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · cil_checked_steps
      simp only [List.append_nil, Nat.reduceAdd, leaveFrame, List.foldl_nil]
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [run, cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]))

/-- Ordinary access and private locals suffice; caller references may overlap since the carry is read first. -/
theorem carry_body_succeeds_of_run (cw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64)
    (runs : CarryRun program index body cw)
    (a b c : BitVec 64) (carry output first second : Reference)
    (frame : Frame) (memory : Memory)
    (locals : frame.locals = [.bytes .word64 first, .bytes .word64 second])
    (distinct : first.allocation ≠ second.allocation)
    (privateFirst : carry.allocation ≠ first.allocation)
    (privateSecond : carry.allocation ≠ second.allocation)
    (firstWritable : access memory first 8 1 true = .ok ())
    (secondWritable : access memory second 8 1 true = .ok ())
    (carryReadable : read memory carry 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carry 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ()) :
    ∃ stored,
      run program (body.code.length + 1) index 0
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
        frame [] memory = .ok (leaveFrame frame stored, []) ∧
      read stored output 8 1 = .ok (numberBytes (a + b + c).toNat 8) ∧
      (WordsDisjoint carry output → read stored carry 8 1 = .ok (numberBytes (cw a b c).toNat 8)) ∧
      (∀ id offset, id ≠ first.allocation → id ≠ second.allocation →
        OutsideWord carry id offset → OutsideWord output id offset →
        stored.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory stored := by
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨secondAllocation, secondAccess⟩ := access_requirements secondWritable
  obtain ⟨carryAllocation, carryAccess⟩ := access_requirements carryWritable
  obtain ⟨outputAllocation, outputAccess⟩ := access_requirements outputWritable
  obtain ⟨m1, w0, s0, firstRead, firstLoad⟩ := store_local_word64 (a + b) firstWritable
  have readCarry := write_preserves_disjoint_read w0 carryReadable (Or.inl privateFirst)
  obtain ⟨m2, w1, s1, secondRead, secondLoad⟩ :=
    store_local_word64 (a + b + c) (secondAccess.after_write w0).access
  have retainedFirst := write_preserves_disjoint_read w1 firstRead (Or.inl distinct)
  have carry1 := (carryAccess.after_write w0).access
  have carry2 := ((carryAccess.after_write w0).after_write w1).access
  obtain ⟨m3, wc⟩ := write_succeeds (bytes := numberBytes (cw a b c).toNat 8)
    (by simpa only [length] using carry2)
  have retainedSecond := write_preserves_disjoint_read wc secondRead (Or.inl (Ne.symm privateSecond))
  have output3 := (((outputAccess.after_write w0).after_write w1).after_write wc).access
  obtain ⟨m4, wo⟩ := write_succeeds (bytes := numberBytes (a + b + c).toNat 8)
    (by simpa only [length] using output3)
  refine ⟨m4, runs a b c carry output first second frame memory m1 m2 m3 m4
    locals s0 s1 firstLoad (load_word64_of_read readCarry)
    (load_local_word64_of_read retainedFirst) secondLoad
    (load_local_word64_of_read retainedSecond)
    (access_reference_valid _ _ _ _ _ carry1) (access_reference_valid _ _ _ _ _ carry2)
    (access_reference_valid _ _ _ _ _ output3) wc wo, ?_, ?_, ?_, ?_⟩
  · simpa only [length] using write_readback _ _ _ _ _ wo
  · intro disjoint
    have carryRead : read m3 carry 8 1 = .ok (numberBytes (cw a b c).toNat 8) := by
      simpa only [length] using write_readback _ _ _ _ _ wc
    exact write_preserves_disjoint_read wo carryRead (by simpa only [WordsDisjoint, length] using disjoint)
  · intro id offset notFirst notSecond outsideCarry outsideOutput
    rw [write_word_outside wo id offset outsideOutput,
      write_word_outside wc id offset outsideCarry,
      write_word_outside w1 id offset (Or.inl notSecond),
      write_word_outside w0 id offset (Or.inl notFirst)]
  · exact (write_preserves_access_below w0 memory.nextIdentity).trans
      ((write_preserves_access_below w1 memory.nextIdentity).trans
        ((write_preserves_access_below wc memory.nextIdentity).trans
          (write_preserves_access_below wo memory.nextIdentity)))

/-- The helper's two word homes are fresh, writable and private; setup keeps caller memory. -/
theorem carry_frame_setup_of_shape (shape : CarryShape body) (memory : Memory) (args : List Value)
    (wellFormed : memory.WellFormed) :
    ∃ first second frame result,
      enterFrame body args memory = .ok (frame, result) ∧
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
  have entered : enterFrame body args memory = .ok (frame, result) := by
    simp [enterFrame, shape.localKinds, shape.locals, shape.vectorArgs, shape.parameterHomes, makeLocals,
      madeFirst, madeSecond, makeArgumentHomes, makeParameterHomes, frame, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  refine ⟨first, second, frame, result, entered, rfl, rfl, ?_, ?_, readSecond, ?_, writeSecond,
    enterFrame_preserves_caller_memory _ _ _ _ _ entered⟩
  · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le freshFirst.2 freshSecond.1)
  · rw [preserved.read first freshFirst.2 8 1]
    exact readFirst
  · rw [preserved.access first freshFirst.2 8 1 true]
    exact writeFirst

/-- Total checked invocation from caller permissions, including setup and teardown. -/
theorem carry_invoke_succeeds_of_run (cw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64)
    (found : program[index]? = some body) (shape : CarryShape body) (runs : CarryRun program index body cw)
    (a b c : BitVec 64) (carry output : Reference) (memory : Memory)
    (wellFormed : memory.WellFormed)
    (carryReadable : read memory carry 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carry 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ()) :
    ∃ fuel result,
      invoke program fuel index
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
        memory = .ok (result, []) ∧
      loadValue result (.address output) 8 = .ok (.i64 (a + b + c)) ∧
      (WordsDisjoint carry output → loadValue result (.address carry) 8 = .ok (.i64 (cw a b c))) ∧
      (∀ id offset, id < memory.nextIdentity → OutsideWord carry id offset → OutsideWord output id offset →
        result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 8 1 = .ok (numberBytes (a + b + c).toNat 8) ∧
      (WordsDisjoint carry output → read result carry 8 1 = .ok (numberBytes (cw a b c).toNat 8)) := by
  let args := [Value.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
  have fc := access_reference_valid _ _ _ _ _ carryWritable
  have fo := access_reference_valid _ _ _ _ _ outputWritable
  obtain ⟨ca, cp, _, _⟩ := formed_reference_live _ _ _ fc
  obtain ⟨oa, op, _, _⟩ := formed_reference_live _ _ _ fo
  have carryOld := (wellFormed.1 _ _ cp).1
  have outputOld := (wellFormed.1 _ _ op).1
  obtain ⟨first, second, frame, enteredMemory, entered, locals, owned, distinct,
    _, _, firstWritable, secondWritable, preserved⟩ := carry_frame_setup_of_shape shape memory args wellFormed
  have fresh := enterFrame_fresh _ _ _ _ _ entered
  have firstNew := (fresh.2 first.allocation (by rw [owned]; simp)).1
  have secondNew := (fresh.2 second.allocation (by rw [owned]; simp)).1
  have readCarry : read enteredMemory carry 8 1 = .ok (numberBytes c.toNat 8) := by
    rw [preserved.read carry carryOld 8 1]; exact carryReadable
  have writeCarry : access enteredMemory carry 8 1 true = .ok () := by
    rw [preserved.access carry carryOld 8 1 true]; exact carryWritable
  have writeOutput : access enteredMemory output 8 1 true = .ok () := by
    rw [preserved.access output outputOld 8 1 true]; exact outputWritable
  obtain ⟨stored, executed, outputRead, carryRead, footprint, retainedAccess⟩ :=
    carry_body_succeeds_of_run cw runs a b c carry output first second
      frame enteredMemory locals distinct (Nat.ne_of_lt (Nat.lt_of_lt_of_le carryOld firstNew))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le carryOld secondNew))
      firstWritable secondWritable readCarry writeCarry writeOutput
  have returned := leaveFrame_preserves_memory_below frame stored memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  have outputRead' : read (leaveFrame frame stored) output 8 1 = .ok (numberBytes (a + b + c).toNat 8) := by
    rw [returned.read output outputOld 8 1]; exact outputRead
  refine ⟨body.code.length + 1, leaveFrame frame stored, ?_,
    load_word64_of_read outputRead', ?_, ?_, ?_, outputRead', ?_⟩
  · have checked : args.mapM (checkedValue memory) = .ok args := by
      simp [args, checkedValue, numericValue, formValue, fc, fo, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    change invoke program _ index args memory = _
    simpa only [invoke, found, checked, entered, Except.mapError, Bind.bind, Except.bind] using executed
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

#print axioms carry_body_succeeds_of_run
#print axioms carry_frame_setup_of_shape
#print axioms carry_invoke_succeeds_of_run

end UInt256Proof.Add.CarrySafety
