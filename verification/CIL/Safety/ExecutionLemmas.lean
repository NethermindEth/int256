import CIL.Safety.Execution
namespace CIL.Safety
theorem run_success_step (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (result : List Value)
    (success : run program (fuel + 1) method pc args frame stack m = .ok (final, result)) :
    ∃ body op action, program[method]? = some body ∧ body.code[pc]? = some op ∧
      step body op pc args frame stack m = .ok action := by
  cases hb : program[method]? with
  | none => simp [run, hb] at success
  | some body =>
    cases ho : body.code[pc]? with
    | none => simp [run, hb, ho] at success
    | some op =>
      cases hs : step body op pc args frame stack m with
      | error fault => simp [run, hb, ho, hs, Bind.bind, Except.bind, Except.mapError] at success
      | ok action => exact ⟨body, op, action, rfl, ho, hs⟩
#print axioms run_success_step
end CIL.Safety
