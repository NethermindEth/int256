import UInt256.Safety.PrivateWordAccess
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Model.Safety
open CIL.Safety

/-- Execute two initialized local loads, pass a writable private home to an
    actually proved call, then store its returned word. Instruction identities
    and both memory effects are premises checked by each caller. -/
theorem run_local_word_call {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method}
    {args rest : List Value} {frame : Frame} {original entered current : Memory}
    {inputs outputs : List Reference} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity body.localKinds frame.locals)
    (left right target result : Nat) (a b stored returned : BitVec 64)
    (leftKnown : known left = some a) (rightKnown : known right = some b)
    (targetKind : body.localKinds[target]? = some .word64)
    (resultKind : body.localKinds[result]? = some .word64)
    (found : program[method]? = some body)
    (code0 : body.code[pc]? = some (.local left))
    (code1 : body.code[pc + 1]? = some (.local right))
    (code2 : body.code[pc + 2]? = some (.localAddr target))
    (code3 : body.code[pc + 3]? = some (.call callee 3))
    (code4 : body.code[pc + 4]? = some (.setLocal result))
    (effect : ∀ reference, frame.locals[target]? = some (.bytes .word64 reference) →
      access current reference 8 1 true = .ok () →
      ∃ fuel after,
        invoke program fuel callee [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current =
          .ok (after, [.scalar (.i64 returned)]) ∧
        after.WellFormed ∧ read after reference 8 1 = .ok (numberBytes stored.toNat 8) ∧
        AccessBelow current.nextIdentity current after ∧
        (∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
          after.cells id offset = current.cells id offset))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord (rememberWord known target stored) result returned) →
      ∃ fuel final values, run program fuel method (pc + 5) args frame rest after =
        .ok (final, values) ∧ post final values) :
    ∃ fuel final values, run program fuel method pc args frame rest current =
      .ok (final, values) ∧ post final values := by
  obtain ⟨reference, slot, ready, formed⟩ := state.home enteredWF homes target targetKind
  apply run_next_exists post found code0 (state.snapshots.load a leftKnown)
  apply run_next_exists post found code1 (state.snapshots.load b rightKnown)
  have addressRest : step body (.localAddr target) (pc + 2) args frame
      (.scalar (.i64 b) :: .scalar (.i64 a) :: rest) current =
      .ok (.next (pc + 3) (.reference (.address reference) :: .scalar (.i64 b) :: .scalar (.i64 a) :: rest) frame current) := by
    simp [step, localAddress, slot, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply run_next_exists post found code2 addressRest
  obtain ⟨childFuel, after, invoked, wf, loaded, authority, outside⟩ := effect reference slot ready
  have updated := state.after_word_call originalCall homes childFuel callee _ _ invoked
    target reference stored slot wf loaded authority outside
  obtain ⟨prepared, written, preparedState⟩ := updated.store enteredWF homes result resultKind returned
    (pc + 4) args rest (body := body)
  have tail := run_next_exists post found code4 written (by
    simpa only [Nat.add_assoc] using continuation prepared preparedState)
  obtain ⟨tailFuel, final, values, resumed, satisfied⟩ := tail
  have stepped : step body (.call callee 3) (pc + 3) args frame
      (.reference (.address reference) :: .scalar (.i64 b) :: .scalar (.i64 a) :: rest) current =
      .ok (.call callee [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] rest current) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, ran⟩ := run_call_exists found code3 stepped ⟨childFuel, invoked⟩
    ⟨tailFuel, by simpa only [Nat.add_assoc, Nat.reduceAdd, List.cons_append, List.nil_append] using resumed⟩
  exact ⟨fuel, final, values, ran, satisfied⟩

#print axioms run_local_word_call
end UInt256Model.Safety
