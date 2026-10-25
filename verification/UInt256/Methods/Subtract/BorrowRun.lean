import CIL.Safety.StepComposition
import CIL.Safety.SymbolicExecution
import CIL.Safety.WordFootprint
import CIL.Safety.CallComposition
import CIL.Safety.MethodContract

namespace UInt256Proof.Subtract.Profile
variable {program : CIL.Program} {index : Nat} {body : CIL.Method}

open CIL.Safety

/-- Frame metadata `enterFrame` reads; any other shape fails these equalities. -/
structure BorrowShape (body : CIL.Method) : Prop where
  localKinds : body.localKinds = []
  locals : body.locals = []
  vectorArgs : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []

/-- A local-free borrow body whose only effects are the difference write, then the borrow write `bw`. -/
def BorrowRun (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (bw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ (a b c : BitVec 64) (borrow output : Reference) (frame : Frame) (memory stored final : Memory),
    form memory borrow = .ok borrow → form memory output = .ok output → form stored borrow = .ok borrow →
    loadValue memory (.address borrow) 8 = .ok (.i64 c) → loadValue stored (.address borrow) 8 = .ok (.i64 c) →
    write memory output (numberBytes (a - b - c).toNat 8) 1 = .ok stored →
    write stored borrow (numberBytes (bw a b c).toNat 8) 1 = .ok final →
    run program (body.code.length + 1) index 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrow), .reference (.address output)]
      frame [] memory = .ok (leaveFrame frame final, [])

set_option hygiene false in
/-- Prove `BorrowRun` by stepping every fetched instruction and frameless pure call; `normalize` evaluates the borrow write. -/
macro "borrow_run_steps " "[" normalize:term,* "]" : tactic => `(tactic| (
  intro a b c borrow output frame memory stored final borrowFormed outputFormed borrowStored beforeRead
    afterRead resultWrite borrowWrite
  simp only [cil_code]
  repeat' first
    | (apply Eq.trans
       · apply run_next
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · cil_fact_simp (config := { implicitDefEqProofs := false })
             [cil_code, step, observerCount, checkedValue, numericValue, formValue, pureArity, scalars, CIL.step.eq_def,
               CIL.binary, CIL.unary, instruction, storeValue, referenceAt, checkedAt,
               Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
             [borrowFormed, outputFormed, borrowStored, beforeRead, afterRead, resultWrite, borrowWrite,
               $[$normalize:term],*]
           exact ⟨rfl, rfl, rfl, rfl⟩)
    | (apply run_call_of_invoke
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, step, cil_guard, observerCount, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind,
           Pure.pure, Except.pure]
         exact ⟨rfl, rfl, rfl, rfl⟩
       · cil_checked_steps
       simp only [List.append_nil, List.cons_append, List.nil_append, Nat.reduceAdd, leaveFrame, List.foldl_nil])
    | (solve
       | rw [run]
         simp (config := { implicitDefEqProofs := false })
           [cil_code, step, cil_guard, observerCount, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
  simp [run, cil_code, step, cil_guard, observerCount, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]))

/-- The incoming borrow is reread after the difference write, so the words must be disjoint. -/
theorem borrow_invoke_succeeds_of_run (bw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64)
    (found : program[index]? = some body) (shape : BorrowShape body) (runs : BorrowRun program index body bw)
    (a b c : BitVec 64) (borrowRef output : Reference) (memory : Memory)
    (readable : read memory borrowRef 8 1 = .ok (numberBytes c.toNat 8))
    (writable : access memory borrowRef 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowRef output) :
    ∃ fuel final,
      invoke program fuel index
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
        memory = .ok (final, []) ∧
      Confined [(borrowRef, 8), (output, 8)] memory final ∧
      read final output 8 1 = .ok (numberBytes (a - b - c).toNat 8) ∧
      read final borrowRef 8 1 = .ok (numberBytes (bw a b c).toNat 8) := by
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨allocation, authority⟩ := access_requirements writable
  obtain ⟨stored, resultWrite⟩ := write_succeeds (bytes := numberBytes (a - b - c).toNat 8)
    (by simpa only [length] using outputWritable)
  have retained := write_preserves_disjoint_read resultWrite readable
    (by simpa only [WordsDisjoint, length] using disjoint)
  have borrowWritable := (authority.after_write resultWrite).access
  obtain ⟨final, borrowWrite⟩ := write_succeeds (bytes := numberBytes (bw a b c).toNat 8)
    (by simpa only [length] using borrowWritable)
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  have fb := access_reference_valid _ _ _ _ _ writable
  have fo := access_reference_valid _ _ _ _ _ outputWritable
  have ran := runs a b c borrowRef output frame memory stored final fb fo
    (access_reference_valid _ _ _ _ _ borrowWritable) (load_word64_of_read readable)
    (load_word64_of_read retained) resultWrite borrowWrite
  simp only [leaveFrame, frame, List.foldl_nil] at ran
  have setup : enterFrame body
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
      memory = .ok (frame, memory) := by
    simp [enterFrame, shape.localKinds, shape.locals, shape.vectorArgs, shape.parameterHomes, makeSelectedLocals, makeLocals, makeSelectedLocalsFrom, ite_self,
      makeArgumentHomes, makeParameterHomes, frame, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have invoked : invoke program (body.code.length + 1) index
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
      memory = .ok (final, []) := by
    refine invoke_of_run found ?_ setup ran
    simp [checkedValue, numericValue, formValue, fb, fo, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨_, final, invoked,
    (Confined.write resultWrite (by simp [numberBytes])).trans (Confined.write borrowWrite (by simp [numberBytes])),
    ?_, by simpa only [length] using write_readback _ _ _ _ _ borrowWrite⟩
  have readback : read stored output 8 1 = .ok (numberBytes (a - b - c).toNat 8) := by
    simpa only [length] using write_readback _ _ _ _ _ resultWrite
  apply write_preserves_disjoint_read borrowWrite readback
  rcases disjoint with distinct | before | after
  · exact Or.inl (Ne.symm distinct)
  · exact Or.inr (Or.inr (by simpa only [length] using before))
  · exact Or.inr (Or.inl (by simpa only [length] using after))

#print axioms borrow_invoke_succeeds_of_run
end UInt256Proof.Subtract.Profile
