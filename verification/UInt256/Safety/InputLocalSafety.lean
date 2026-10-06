import UInt256.Safety.PrivateWordAccess
import CIL.Safety.StepComposition

namespace UInt256Model.Safety
open CIL.Safety

/-- Check the actual argument/field/store sequence. The remembered local value
    comes from the initial input bytes, including when caller ranges overlap. -/
theorem run_input_to_local {program : CIL.Program} {method pc argument target : Nat} {body : CIL.Method}
    {args rest : List Value} {frame : Frame} {original entered current : Memory}
    {inputs outputs : List Reference} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity body.localKinds frame.locals)
    (input : Reference) (member : input ∈ inputs) (index : Fin 4)
    (argumentValue : args[argument]? = some (.reference (.address input)))
    (targetKind : body.localKinds[target]? = some .word64)
    (found : program[method]? = some body)
    (code0 : body.code[pc]? = some (.arg argument))
    (code1 : body.code[pc + 1]? = some (.field index))
    (code2 : body.code[pc + 2]? = some (.setLocal target))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord known target (inputLimb original input index)) →
      ∃ fuel final values, run program fuel method (pc + 3) args frame rest after =
        .ok (final, values) ∧ post final values) :
    ∃ fuel final values, run program fuel method pc args frame rest current =
      .ok (final, values) ∧ post final values := by
  have formed := state.call.input_formed member
  have reading := state.input_field originalCall input member index rest
  apply run_next_exists post found code0
  · simp [step, argumentValue, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found code1
  · simp [step, pureArity, reading, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes target targetKind
    (inputLimb original input index) (pc + 2) args rest (body := body)
  exact run_next_exists post found code2 stored (by simpa only [Nat.add_assoc] using continuation after next)

#print axioms run_input_to_local
end UInt256Model.Safety
