import CIL.Safety.ExecutionInvariants
namespace CIL.Safety

/-- A step at an actual fetched instruction, not an arbitrary instruction body. -/
def ProgramStep (program : CIL.Program) (method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction) : Prop :=
  ∃ body op, program[method]? = some body ∧ body.code[pc]? = some op ∧
    step body op pc args frame stack m = .ok action

theorem programStep_preserves_wellFormed (program : CIL.Program) (method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction)
    (hm : m.WellFormed) (hs : ProgramStep program method pc args frame stack m action) :
    action.memory.WellFormed := by
  obtain ⟨body, op, _, _, hs⟩ := hs
  exact step_preserves_wellFormed _ _ _ _ _ _ _ _ hm hs

/-- A nested call or constructor invokes exactly these captured arguments. -/
def FrameAction.child (action : FrameAction) (callee : Nat) (arguments : List Value) : Prop :=
  (∃ rest, action = .call callee arguments rest action.memory) ∨
  ∃ rest frame temporary, action = .construct callee arguments rest frame temporary action.memory

/-- Memory observations at CIL boundaries, including prefixes of executions
    which later fault. Continuation requires an actual successful child run. -/
inductive RunVisits (program : CIL.Program) : Nat → Nat → Nat → List Value → Frame →
    List Value → Memory → Memory → Prop where
  | initial {fuel method pc args frame stack m} :
      RunVisits program fuel method pc args frame stack m m
  | stepped {fuel method pc args frame stack m action}
      (step : ProgramStep program method pc args frame stack m action) :
      RunVisits program (fuel + 1) method pc args frame stack m action.memory
  | next {fuel method pc args frame stack m target values nextFrame updated observed}
      (step : ProgramStep program method pc args frame stack m (.next target values nextFrame updated))
      (later : RunVisits program fuel method target args nextFrame values updated observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | entered {fuel method pc args frame stack m action callee arguments child childFrame childMemory}
      (step : ProgramStep program method pc args frame stack m action)
      (call : action.child callee arguments) (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory)) :
      RunVisits program (fuel + 1) method pc args frame stack m childMemory
  | child {fuel method pc args frame stack m action callee arguments child childFrame childMemory observed}
      (step : ProgramStep program method pc args frame stack m action)
      (call : action.child callee arguments) (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory))
      (later : RunVisits program fuel callee 0 arguments childFrame [] childMemory observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | callContinue {fuel method pc args frame stack m callee arguments rest updated child
        childFrame childMemory returned result observed}
      (step : ProgramStep program method pc args frame stack m (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory = .ok (returned, result))
      (later : RunVisits program fuel method (pc + 1) args frame (result ++ rest) returned observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | constructContinue {fuel method pc args frame stack m callee arguments rest nextFrame temporary
        updated child childFrame childMemory returned value observed}
      (step : ProgramStep program method pc args frame stack m
        (.construct callee arguments rest nextFrame temporary updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory = .ok (returned, []))
      (load : loadValue returned (.address temporary) (localWidth .vector256) = .ok value)
      (later : RunVisits program fuel method (pc + 1) args nextFrame (.scalar value :: rest) returned observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | expired {fuel method pc args frame stack m result updated}
      (step : ProgramStep program method pc args frame stack m (.returned result updated)) :
      RunVisits program (fuel + 1) method pc args frame stack m (leaveFrame frame updated)

theorem runVisits_wellFormed {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed)
    (hm : m.WellFormed) : observed.WellFormed := by
  induction visit with
  | initial => exact hm
  | stepped step => exact programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
  | next step later ih => exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | entered step call lookup enter =>
    exact enterFrame_preserves_wellFormed _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter
  | child step call lookup enter later ih =>
    exact ih (enterFrame_preserves_wellFormed _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter)
  | callContinue step lookup enter finish later ih =>
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
      (enterFrame_preserves_wellFormed _ _ _ _ _
        (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter) finish)
  | constructContinue step lookup enter finish load later ih =>
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
      (enterFrame_preserves_wellFormed _ _ _ _ _
        (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter) finish)
  | expired step =>
    exact leaveFrame_preserves_wellFormed _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)

#print axioms runVisits_wellFormed

theorem run_success_visits (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    RunVisits program fuel method pc args frame stack m final := by
  induction fuel generalizing method pc args frame stack m final values with
  | zero => cases h
  | succ fuel ih =>
    cases hb : program[method]? with
    | none => simp [run, hb] at h
    | some body =>
      cases ho : body.code[pc]? with
      | none => simp [run, hb, ho] at h
      | some op =>
        cases hs : step body op pc args frame stack m with
        | error fault => simp [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] at h
        | ok action =>
          have actual : ProgramStep program method pc args frame stack m action := ⟨body, op, hb, ho, hs⟩
          cases action with
          | next target stack' frame' memory =>
            simp only [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] at h
            exact .next actual (ih method target args frame' stack' memory final values h)
          | returned result memory =>
            cases hr : result.mapM (checkedValue (leaveFrame frame memory)) <;>
              simp only [run, hb, ho, hs, hr, Except.mapError, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
            · cases h
            · cases h
              exact .expired actual
          | call callee arguments rest memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  exact .callContinue actual hc he hr
                    (ih method (pc + 1) args frame (result ++ rest) memory' final values h)
          | construct callee arguments rest frame' temporary memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  cases result with
                  | cons value rest' => simp at h
                  | nil =>
                    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false] at h
                    cases hl : loadValue memory' (.address temporary) (localWidth .vector256) <;>
                      simp only [hl] at h
                    · cases h
                    · rename_i value
                      exact .constructContinue actual hc he hr hl
                        (ih method (pc + 1) args frame' (.scalar value :: rest) memory' final values h)

#print axioms run_success_visits
end CIL.Safety
