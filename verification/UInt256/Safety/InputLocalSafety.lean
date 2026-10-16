import UInt256.Safety.LocalCallSafety

namespace UInt256Model.Safety
open CIL.Safety

theorem run_input_to_local {program : CIL.Program} {method pc argument target : Nat} {body : CIL.Method}
    {original entered current : Memory} {inputs outputs : List Reference} {frame : Frame}
    {known : Nat → Option (BitVec 64)} {args rest : List Value} {kinds : List CIL.LocalKind}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs) (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (input : Reference) (member : input ∈ inputs) (limb : Fin 4)
    (arg : args[argument]? = some (.reference (.address input)))
    (kind : kinds[target]? = some .word64)
    (found : program[method]? = some body)
    (code0 : body.code[pc]? = some (.arg argument))
    (code1 : body.code[pc + 1]? = some (.fieldAt (8 * limb.val) 8))
    (code2 : body.code[pc + 2]? = some (.setLocal target))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord known target (inputLimb original input limb)) →
      ∃ fuel final returned, run program fuel method (pc + 3) args frame rest after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel method pc args frame rest current = .ok (final, returned) ∧ post final returned := by
  have formed := state.call.input_formed member
  have reading := state.input_field originalCall input member limb rest
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes target kind (inputLimb original input limb)
    (pc + 2) args rest (body := body)
  apply run_next_exists post found code0
  · simp [step, arg, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl,rfl,rfl,rfl⟩
  apply run_next_exists post found code1
  · simp [step, pureArity, reading, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl,rfl,rfl,rfl⟩
  exact run_next_exists post found code2 stored (by simpa only [Nat.add_assoc] using continuation after next)

#print axioms run_input_to_local
end UInt256Model.Safety
