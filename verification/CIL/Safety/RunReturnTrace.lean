import CIL.Safety.RunningPrefixes

namespace CIL.Safety

/-- Every normal interpreter result comes from an actual fetched return reached
    through the running-prefix relation, followed by teardown and result checks. -/
theorem run_success_return_trace (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory) (values : List Value)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ∃ lastPc lastFrame lastStack before returned raw,
      RunningVisits program fuel method pc args frame stack m args lastFrame lastStack before ∧
      ProgramStep program method lastPc args lastFrame lastStack before (.returned raw returned) ∧
      final = leaveFrame lastFrame returned ∧ raw.mapM (checkedValue final) = .ok values := by
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
            obtain ⟨lp, lf, ls, before, returned, raw, visit, fetched, ended, checked⟩ :=
              ih method target args frame' stack' memory final values h
            exact ⟨lp, lf, ls, before, returned, raw, .next actual visit, fetched, ended, checked⟩
          | returned result memory =>
            cases hr : result.mapM (checkedValue (leaveFrame frame memory)) <;>
              simp only [run, hb, ho, hs, hr, Except.mapError, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
            · cases h
            · cases h
              exact ⟨pc, frame, stack, m, memory, result, .initial, actual, rfl, hr⟩
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
                  obtain ⟨lp, lf, ls, before, returned, raw, visit, fetched, ended, checked⟩ :=
                    ih method (pc + 1) args frame (result ++ rest) memory' final values h
                  exact ⟨lp, lf, ls, before, returned, raw,
                    .callContinue actual hc he hr visit, fetched, ended, checked⟩
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
                      obtain ⟨lp, lf, ls, before, returned, raw, visit, fetched, ended, checked⟩ :=
                        ih method (pc + 1) args frame' (.scalar value :: rest) memory' final values h
                      exact ⟨lp, lf, ls, before, returned, raw,
                        .constructContinue actual hc he hr hl visit, fetched, ended, checked⟩

theorem run_success_live_return_trace (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory) (values : List Value)
    (state : LiveState program args frame stack m)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ∃ lastPc lastFrame lastStack before returned raw,
      RunningVisits program fuel method pc args frame stack m args lastFrame lastStack before ∧
      LiveState program args lastFrame lastStack before ∧
      ProgramStep program method lastPc args lastFrame lastStack before (.returned raw returned) ∧
      final = leaveFrame lastFrame returned ∧ raw.mapM (checkedValue final) = .ok values ∧
      ReturnedState program final values := by
  obtain ⟨lastPc, lastFrame, lastStack, before, returned, raw, visit, fetched, ended, checked⟩ :=
    run_success_return_trace _ _ _ _ _ _ _ _ _ _ h
  exact ⟨lastPc, lastFrame, lastStack, before, returned, raw, visit,
    runningVisits_live_state visit state, fetched, ended, checked,
    run_returned_state _ _ _ _ _ _ _ _ _ _ state h⟩

#print axioms run_success_return_trace
#print axioms run_success_live_return_trace

end CIL.Safety
