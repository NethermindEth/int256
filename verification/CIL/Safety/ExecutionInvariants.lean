import CIL.Safety.Execution
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.StaticMemoryLemmas
namespace CIL.Safety

def FrameAction.memory : FrameAction → Memory
  | .next _ _ _ m | .call _ _ _ m | .construct _ _ _ _ _ m | .returned _ m => m

theorem step_preserves_wellFormed (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed)
    (h : step body operation pc args frame stack m = .ok action) : action.memory.WellFormed := by
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact hm
      | solve | apply storeLocal_preserves_wellFormed _ _ _ _ _ hm; assumption
      | solve | apply staticInstruction_preserves_wellFormed _ _ _ _ _ _ _ hm; assumption
      | solve | apply instruction_preserves_wellFormed _ _ _ _ _ hm; assumption
      | solve |
          apply storeValue_preserves_wellFormed
          · apply allocateHome_preserves_wellFormed _ _ _ _ _ hm; assumption
          · assumption
      | cases h
      | split at h

#print axioms step_preserves_wellFormed

theorem run_preserves_wellFormed (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (hm : m.WellFormed)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    final.WellFormed := by
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
          have hw := step_preserves_wellFormed _ _ _ _ _ _ _ _ hm hs
          cases action with
          | next target stack' frame' memory =>
            simp only [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] at h
            exact ih method target args frame' stack' memory final values hw h
          | returned result memory =>
            cases hr : result.mapM (checkedValue (leaveFrame frame memory)) <;>
              simp only [run, hb, ho, hs, hr, Except.mapError, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
            · cases h
            · cases h
              exact leaveFrame_preserves_wellFormed _ _ hw
          | call callee arguments rest memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw he
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  have returnedWF := ih callee 0 arguments childFrame [] childMemory memory' result childWF hr
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  exact ih method (pc + 1) args frame (result ++ rest) memory' final values returnedWF h
          | construct callee arguments rest frame' temporary memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw he
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  have returnedWF := ih callee 0 arguments childFrame [] childMemory memory' result childWF hr
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  split at h
                  · cases h
                  · cases hl : loadValue memory' (.address temporary) (localWidth .vector256) <;>
                      simp only [hl] at h
                    · cases h
                    · rename_i value
                      exact ih method (pc + 1) args frame' (.scalar value :: rest) memory' final values returnedWF h

#print axioms run_preserves_wellFormed

theorem invoke_preserves_wellFormed (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (hm : m.WellFormed)
    (h : invoke program fuel method args m = .ok (final, values)) : final.WellFormed := by
  unfold invoke at h
  cases hb : program[method]? with
  | none => simp [hb] at h
  | some body =>
    cases ha : args.mapM (checkedValue m) <;>
      simp only [hb, ha, Except.mapError, Bind.bind, Except.bind] at h
    · cases h
    · rename_i arguments
      cases he : enterFrame body arguments m <;> simp only [he] at h
      · cases h
      · rename_i entered
        obtain ⟨frame, memory⟩ := entered
        exact run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
          (enterFrame_preserves_wellFormed _ _ _ _ _ hm he) h

#print axioms invoke_preserves_wellFormed
end CIL.Safety
