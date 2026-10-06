import CIL.Safety.FrameStaticWorld
import CIL.Safety.ExecutionFrameOwnership
import CIL.Safety.StaticLifetime

namespace CIL.Safety

/-- Static selection comes from the actual extracted method metadata. -/
def programStaticDescriptors (program : CIL.Program) : List CIL.StaticDescriptor :=
  program.flatMap fun body => body.staticSites.map Prod.snd

theorem program_static_sites_valid (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (found : program[method]? = some body) : StaticSitesValid (programStaticDescriptors program) body := by
  intro site member
  apply List.mem_flatMap.mpr
  refine ⟨body, List.mem_of_getElem? found, ?_⟩
  exact List.mem_map.mpr ⟨site, member, rfl⟩

theorem step_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (body : CIL.Method) (operation : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction)
    (hm : m.WellFormed) (sites : StaticSitesValid descriptors body)
    (world : StaticWorldValid descriptors m)
    (h : step body operation pc args frame stack m = .ok action) :
    StaticWorldValid descriptors action.memory := by
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact world
      | solve | apply storeLocal_preserves_static_world _ _ _ _ _ _ world; assumption
      | solve | apply staticInstruction_preserves_static_world _ _ _ _ _ _ _ _ hm sites world; assumption
      | solve | apply instruction_preserves_static_world _ _ _ _ _ _ world; assumption
      | solve |
          apply storeValue_preserves_static_world
          · apply allocateHome_preserves_static_world _ _ _ _ _ _ hm world; assumption
          · assumption
      | cases h
      | split at h

theorem run_preserves_static_world (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned)
    (world : StaticWorldValid (programStaticDescriptors program) m)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    StaticWorldValid (programStaticDescriptors program) final := by
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
          have updated := step_preserves_static_world _ _ _ _ _ _ _ _ _ hm
            (program_static_sites_valid _ _ _ hb) world hs
          have ownership := step_preserves_frame_allocations _ _ _ _ _ _ _ _ hm owns hs
          cases action with
          | next target stack' frame' memory =>
            simp only [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] at h
            exact ih method target args frame' stack' memory final values hw ownership updated h
          | returned result memory =>
            cases hr : result.mapM (checkedValue (leaveFrame frame memory)) <;>
              simp only [run, hb, ho, hs, hr, Except.mapError, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
            · cases h
            · cases h
              exact leaveFrame_preserves_static_world _ _ _ ownership updated
          | call callee arguments rest memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw he
                have childWorld := enterFrame_preserves_static_world _ _ _ _ _ _ hw updated he
                have childOwn := enterFrame_owned _ _ _ _ _ he
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  have returnedWF := run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ childWF hr
                  have returnedWorld := ih callee 0 arguments childFrame [] childMemory memory' result
                    childWF childOwn childWorld hr
                  have parentOwn := child_run_preserves_parent_frame _ _ _ _ _ _ _ _ _ _ _ hw ownership he hr
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  exact ih method (pc + 1) args frame (result ++ rest) memory' final values
                    returnedWF parentOwn returnedWorld h
          | construct callee arguments rest frame' temporary memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw he
                have childWorld := enterFrame_preserves_static_world _ _ _ _ _ _ hw updated he
                have childOwn := enterFrame_owned _ _ _ _ _ he
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  have returnedWF := run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ childWF hr
                  have returnedWorld := ih callee 0 arguments childFrame [] childMemory memory' result
                    childWF childOwn childWorld hr
                  have parentOwn := child_run_preserves_parent_frame _ _ _ _ _ _ _ _ _ _ _ hw ownership he hr
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  split at h
                  · cases h
                  · cases hl : loadValue memory' (.address temporary) (localWidth .vector256) <;>
                      simp only [hl] at h
                    · cases h
                    · rename_i value
                      exact ih method (pc + 1) args frame' (.scalar value :: rest) memory' final values
                        returnedWF parentOwn returnedWorld h

theorem invoke_preserves_static_world (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (hm : m.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) m)
    (h : invoke program fuel method args m = .ok (final, values)) :
    StaticWorldValid (programStaticDescriptors program) final := by
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
        exact run_preserves_static_world _ _ _ _ _ _ _ _ _ _
          (enterFrame_preserves_wellFormed _ _ _ _ _ hm he)
          (enterFrame_owned _ _ _ _ _ he)
          (enterFrame_preserves_static_world _ _ _ _ _ _ hm world he) h

theorem programStep_preserves_static_world {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (step : ProgramStep program method pc args frame stack m action) (hm : m.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) m) :
    StaticWorldValid (programStaticDescriptors program) action.memory := by
  obtain ⟨body, op, found, _, success⟩ := step
  exact step_preserves_static_world _ _ _ _ _ _ _ _ _ hm
    (program_static_sites_valid _ _ _ found) world success

theorem programStep_preserves_frame_allocations {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (step : ProgramStep program method pc args frame stack m action) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned) :
    FrameAllocations action.memory (action.frameAfter frame).activation (action.frameAfter frame).owned := by
  obtain ⟨body, op, _, _, success⟩ := step
  exact step_preserves_frame_allocations _ _ _ _ _ _ _ _ hm owns success

/-- This invariant holds at actual instruction boundaries, nested calls and
    teardown, even when a later instruction faults. -/
theorem runVisits_preserves_static_world {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned)
    (world : StaticWorldValid (programStaticDescriptors program) m) :
    StaticWorldValid (programStaticDescriptors program) observed := by
  induction visit with
  | initial => exact world
  | stepped step => exact programStep_preserves_static_world step hm world
  | next step later ih =>
    exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
      (programStep_preserves_frame_allocations step hm owns)
      (programStep_preserves_static_world step hm world)
  | entered step call lookup enter =>
    exact enterFrame_preserves_static_world _ _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
      (programStep_preserves_static_world step hm world) enter
  | child step call lookup enter later ih =>
    have hw := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
    have updated := programStep_preserves_static_world step hm world
    exact ih (enterFrame_preserves_wellFormed _ _ _ _ _ hw enter)
      (enterFrame_owned _ _ _ _ _ enter)
      (enterFrame_preserves_static_world _ _ _ _ _ _ hw updated enter)
  | callContinue step lookup enter finish later ih =>
    have hw := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
    have updated := programStep_preserves_static_world step hm world
    have ownership := programStep_preserves_frame_allocations step hm owns
    have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw enter
    have childWorld := enterFrame_preserves_static_world _ _ _ _ _ _ hw updated enter
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ childWF finish)
      (child_run_preserves_parent_frame _ _ _ _ _ _ _ _ _ _ _ hw ownership enter finish)
      (run_preserves_static_world _ _ _ _ _ _ _ _ _ _ childWF
        (enterFrame_owned _ _ _ _ _ enter) childWorld finish)
  | constructContinue step lookup enter finish load later ih =>
    have hw := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
    have updated := programStep_preserves_static_world step hm world
    have ownership := programStep_preserves_frame_allocations step hm owns
    have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ hw enter
    have childWorld := enterFrame_preserves_static_world _ _ _ _ _ _ hw updated enter
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ childWF finish)
      (child_run_preserves_parent_frame _ _ _ _ _ _ _ _ _ _ _ hw ownership enter finish)
      (run_preserves_static_world _ _ _ _ _ _ _ _ _ _ childWF
        (enterFrame_owned _ _ _ _ _ enter) childWorld finish)
  | expired step =>
    exact leaveFrame_preserves_static_world _ _ _
      (programStep_preserves_frame_allocations step hm owns)
      (programStep_preserves_static_world step hm world)

#print axioms program_static_sites_valid
#print axioms step_preserves_static_world
#print axioms run_preserves_static_world
#print axioms invoke_preserves_static_world
#print axioms runVisits_preserves_static_world

end CIL.Safety
