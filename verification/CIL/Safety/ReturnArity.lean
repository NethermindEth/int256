import CIL.Safety.Certificate

namespace CIL.Safety

/-- A checked return has the arity declared by its actual method body. -/
theorem step_return_length (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory) (values : List Value)
    (executed : step body operation pc args frame stack memory = .ok (.returned values final)) :
    values.length = if body.returnsValue then 1 else 0 := by
  unfold step at executed
  repeat' first
    | solve |
      have same : values = stack := (checkedValues_valid _ _ _ (by assumption)).1
      rw [same]
      simp_all
    | cases executed
    | split at executed
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed

theorem run_return_length (program : CIL.Program) (fuel method pc : Nat) (body : CIL.Method)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory) (values : List Value)
    (lookup : program[method]? = some body)
    (executed : run program fuel method pc args frame stack memory = .ok (final, values)) :
    values.length = if body.returnsValue then 1 else 0 := by
  obtain ⟨lastPc, lastFrame, lastStack, before, returned, raw, _, fetched, _, checked⟩ :=
    run_success_return_trace program fuel method pc args frame stack memory final values executed
  obtain ⟨actualBody, operation, found, _, stepped⟩ := fetched
  rw [lookup] at found
  cases found
  rw [(checkedValues_valid _ _ _ checked).1]
  exact step_return_length body operation lastPc args lastFrame lastStack before returned raw stepped

#print axioms step_return_length
#print axioms run_return_length
end CIL.Safety
