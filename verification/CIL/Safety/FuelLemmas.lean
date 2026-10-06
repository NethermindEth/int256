import CIL.Safety.Execution
namespace CIL.Safety
def Settled (outcome : Except LocatedFault α) : Prop :=
  match outcome with
  | .ok _ => True
  | .error fault => fault.fault ≠ .fuelExhausted

theorem run_mono (program : CIL.Program) (fuel extra method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (outcome : Except LocatedFault (Memory × List Value))
    (ready : Settled outcome)
    (h : run program fuel method pc args frame stack memory = outcome) :
    run program (fuel + extra) method pc args frame stack memory = outcome := by
  induction fuel generalizing method pc args frame stack memory outcome with
  | zero =>
    simp only [run] at h
    subst outcome
    simp [Settled] at ready
  | succ fuel ih =>
    cases hb : program[method]? with
    | none => simpa [Nat.succ_add, run, hb] using h
    | some body =>
      cases ho : body.code[pc]? with
      | none => simpa [Nat.succ_add, run, hb, ho] using h
      | some op =>
        cases hs : step body op pc args frame stack memory with
        | error fault =>
          simpa [Nat.succ_add, run, hb, ho, hs, Bind.bind, Except.bind, Except.mapError] using h
        | ok action =>
          cases action with
          | next target values nextFrame updated =>
            simp [run, hb, ho, hs, Bind.bind, Except.bind, Except.mapError] at h
            simpa [Nat.succ_add, run, hb, ho, hs, Bind.bind, Except.bind, Except.mapError] using
              ih method target args nextFrame values updated outcome ready h
          | returned values updated =>
            simpa [Nat.succ_add, run, hb, ho, hs, Bind.bind, Except.bind, Except.mapError] using h
          | call callee arguments rest updated =>
            cases hc : program[callee]? with
            | none => simpa [Nat.succ_add, run, hb, ho, hs, hc, Bind.bind, Except.bind, Except.mapError] using h
            | some child =>
              cases he : enterFrame child arguments updated with
              | error fault => simpa [Nat.succ_add, run, hb, ho, hs, hc, he, Bind.bind, Except.bind, Except.mapError] using h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp [run, hb, ho, hs, hc, he, hr, Bind.bind, Except.bind, Except.mapError] at h
                  have settled : Settled (.error fault : Except LocatedFault (Memory × List Value)) := by
                    simpa [← h] using ready
                  have more := ih callee 0 arguments childFrame [] childMemory (.error fault) settled hr
                  simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more, Bind.bind, Except.bind, Except.mapError] using h
                | ok childResult =>
                  obtain ⟨final, values⟩ := childResult
                  have more := ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) trivial hr
                  simp [run, hb, ho, hs, hc, he, hr, Bind.bind, Except.bind, Except.mapError] at h
                  have parent := ih method (pc + 1) args frame (values ++ rest) final outcome ready h
                  simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more, Bind.bind, Except.bind, Except.mapError] using parent
          | construct callee arguments rest parentFrame temporary updated =>
            cases hc : program[callee]? with
            | none => simpa [Nat.succ_add, run, hb, ho, hs, hc, Bind.bind, Except.bind, Except.mapError] using h
            | some child =>
              cases he : enterFrame child arguments updated with
              | error fault => simpa [Nat.succ_add, run, hb, ho, hs, hc, he, Bind.bind, Except.bind, Except.mapError] using h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp [run, hb, ho, hs, hc, he, hr, Bind.bind, Except.bind, Except.mapError] at h
                  have settled : Settled (.error fault : Except LocatedFault (Memory × List Value)) := by
                    simpa [← h] using ready
                  have more := ih callee 0 arguments childFrame [] childMemory (.error fault) settled hr
                  simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more, Bind.bind, Except.bind, Except.mapError] using h
                | ok childResult =>
                  obtain ⟨final, values⟩ := childResult
                  have more := ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) trivial hr
                  cases values with
                  | cons value tail =>
                    simpa [Nat.succ_add, run, hb, ho, hs, hc, he, hr, more, Bind.bind, Except.bind, Except.mapError] using h
                  | nil =>
                    cases hv : loadValue final (.address temporary) (localWidth .vector256) with
                    | error fault =>
                      simpa [Nat.succ_add, run, hb, ho, hs, hc, he, hr, more, hv, Bind.bind, Except.bind, Except.mapError] using h
                    | ok value =>
                      simp [run, hb, ho, hs, hc, he, hr, hv, Bind.bind, Except.bind, Except.mapError] at h
                      have parent := ih method (pc + 1) args parentFrame (.scalar value :: rest) final outcome ready h
                      simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more, hv, Bind.bind, Except.bind, Except.mapError] using parent
#print axioms run_mono

theorem invoke_mono (program : CIL.Program) (fuel extra method : Nat)
    (args : List Value) (memory : Memory) (outcome : Except LocatedFault (Memory × List Value))
    (ready : Settled outcome) (h : invoke program fuel method args memory = outcome) :
    invoke program (fuel + extra) method args memory = outcome := by
  cases hb : program[method]? with
  | none => simpa [invoke, hb] using h
  | some body =>
    cases ha : args.mapM (checkedValue memory) with
    | error fault => simpa [invoke, hb, ha, Bind.bind, Except.bind, Except.mapError] using h
    | ok arguments =>
      cases he : enterFrame body arguments memory with
      | error fault => simpa [invoke, hb, ha, he, Bind.bind, Except.bind, Except.mapError] using h
      | ok entered =>
        obtain ⟨frame, updated⟩ := entered
        simp [invoke, hb, ha, he, Bind.bind, Except.bind, Except.mapError] at h
        simpa [invoke, hb, ha, he, Bind.bind, Except.bind, Except.mapError] using
          run_mono program fuel extra method 0 arguments frame [] updated outcome ready h

/-- A classified semantic fault refutes successful execution for every fuel,
    not merely the concrete budget used to exhibit the fault. -/
theorem invoke_fault_refutes_success (program : CIL.Program) (observed method : Nat)
    (args : List Value) (memory : Memory) (fault : LocatedFault)
    (semantic : fault.fault ≠ .fuelExhausted)
    (witness : invoke program observed method args memory = .error fault)
    (fuel : Nat) (result : Memory × List Value) :
    invoke program fuel method args memory ≠ .ok result := by
  intro success
  have failure := invoke_mono program observed fuel method args memory (.error fault) semantic witness
  have returned := invoke_mono program fuel observed method args memory (.ok result) trivial success
  rw [Nat.add_comm] at returned
  rw [failure] at returned
  cases returned

#print axioms invoke_mono
#print axioms invoke_fault_refutes_success
end CIL.Safety
