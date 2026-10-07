import CIL.Safety.Execution
namespace CIL.Safety
/-- Compose checked argument/frame setup with execution. Keeping this boundary
    explicit avoids rechecking an expanded interpreter expression at every call. -/
theorem invoke_of_run {program : CIL.Program} {fuel method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered final : Memory} {result : List Value}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (executed : run program fuel method 0 args frame [] entered = .ok (final, result)) :
    invoke program fuel method args memory = .ok (final, result) := by
  simp only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
  exact executed

theorem run_next {program : CIL.Program} {fuel method pc target : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory}
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next target values nextFrame updated)) :
    run program (fuel + 1) method pc args frame stack memory =
      run program fuel method target args nextFrame values updated := by
  simp only [run, methodFound, instructionFound, stepped, Except.mapError, Bind.bind, Except.bind]
#print axioms run_next

/-- Compose one checked fetched step with a terminating continuation without
    fixing the continuation's fuel in the caller proof. -/
theorem run_next_exists {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory}
    (post : Memory → List Value → Prop)
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next target values nextFrame updated))
    (continuation : ∃ fuel result returned,
      run program fuel method target args nextFrame values updated = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
      post result returned := by
  obtain ⟨fuel, result, returned, finished, satisfied⟩ := continuation
  exact ⟨fuel + 1, result, returned,
    (run_next methodFound instructionFound stepped).trans finished, satisfied⟩

#print axioms run_next_exists
end CIL.Safety
