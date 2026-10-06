import CIL.Safety.FuelLemmas
import CIL.Safety.LiveValues

namespace CIL.Safety

/-- Compose an independently checked invocation with the actual caller step.
    The invocation includes child setup and teardown; no helper body is assumed. -/
theorem run_call_of_invoke {program : CIL.Program} {fuel method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest returned values : List Value}
    {frame : Frame} {memory updated childResult result : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (child : invoke program fuel callee arguments updated = .ok (childResult, returned))
    (continuation : run program fuel method (pc + 1) args frame (returned ++ rest) childResult = .ok (result, values)) :
    run program (fuel + 1) method pc args frame stack memory = .ok (result, values) := by
  cases hb : program[callee]? with
  | none => simp [invoke, hb] at child
  | some childBody =>
    cases ha : arguments.mapM (checkedValue updated) with
    | error fault => simp [invoke, hb, ha, Except.mapError, Bind.bind, Except.bind] at child
    | ok checked =>
      have same := (checkedValues_valid _ _ _ ha).1
      subst checked
      cases he : enterFrame childBody arguments updated with
      | error fault => simp [invoke, hb, ha, he, Except.mapError, Bind.bind, Except.bind] at child
      | ok entered =>
        obtain ⟨childFrame, childMemory⟩ := entered
        simp only [invoke, hb, ha, he, Except.mapError, Bind.bind, Except.bind] at child
        simp only [run, methodFound, instructionFound, stepped, hb, he, child,
          continuation, Except.mapError, Bind.bind, Except.bind]

/-- Independently sufficient budgets combine without requiring equal proof fuel. -/
theorem run_call_exists {program : CIL.Program} {method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest returned values : List Value}
    {frame : Frame} {memory updated childResult result : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (child : ∃ fuel, invoke program fuel callee arguments updated = .ok (childResult, returned))
    (continuation : ∃ fuel, run program fuel method (pc + 1) args frame (returned ++ rest) childResult = .ok (result, values)) :
    ∃ fuel, run program fuel method pc args frame stack memory = .ok (result, values) := by
  obtain ⟨childFuel, child⟩ := child
  obtain ⟨parentFuel, continuation⟩ := continuation
  have hc := invoke_mono program childFuel parentFuel callee arguments updated (.ok (childResult, returned)) trivial child
  have hp := run_mono program parentFuel childFuel method (pc + 1) args frame
    (returned ++ rest) childResult (.ok (result, values)) trivial continuation
  rw [Nat.add_comm parentFuel childFuel] at hp
  exact ⟨childFuel + parentFuel + 1, run_call_of_invoke methodFound instructionFound stepped hc hp⟩

#print axioms run_call_of_invoke
#print axioms run_call_exists

end CIL.Safety
