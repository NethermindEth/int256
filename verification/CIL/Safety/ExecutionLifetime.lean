import CIL.Safety.ExecutionAllocations
import CIL.Safety.ExecutionPrefixes

namespace CIL.Safety

/-- Calls may expire their own homes. Only identities below the caller's
    allocation watermark must retain exactly the same lifetime and layout. -/
structure AllocationsBelow (before after : Memory) (watermark : Nat) : Prop where
  next : before.nextIdentity ≤ after.nextIdentity
  lookup : ∀ id, id < watermark → after.allocations id = before.allocations id

theorem AllocationExtension.below {before after : Memory} (ext : AllocationExtension before after)
    (watermark : Nat) (bound : watermark ≤ before.nextIdentity) :
    AllocationsBelow before after watermark :=
  ⟨ext.next, fun id old => ext.lookup id (Nat.lt_of_lt_of_le old bound)⟩

theorem AllocationsBelow.trans {first middle last : Memory} {watermark : Nat}
    (left : AllocationsBelow first middle watermark) (right : AllocationsBelow middle last watermark) :
    AllocationsBelow first last watermark := by
  refine ⟨Nat.le_trans left.next right.next, ?_⟩
  intro id bound
  rw [right.lookup id bound, left.lookup id bound]

theorem AllocationsBelow.preserves_reference {m result : Memory} {watermark : Nat}
    (ext : AllocationsBelow m result watermark) (r formed : Reference)
    (old : r.allocation < watermark) (h : form m r = .ok formed) :
    form result r = .ok formed := by
  rw [form_allocation_congr _ _ _ (ext.lookup r.allocation old)]
  exact h

theorem run_preserves_caller_allocations (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (watermark : Nat) (bound : watermark ≤ m.nextIdentity)
    (owned : frame.OwnedAbove watermark)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    AllocationsBelow m final watermark := by
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
          have ext := step_extends_allocations _ _ _ _ _ _ _ _ hs
          have afterBound := Nat.le_trans bound ext.next
          have afterOwned := step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound hs
          have first := ext.below watermark bound
          cases action with
          | next target stack' frame' memory =>
            simp only [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] at h
            exact first.trans (ih method target args frame' stack' memory final values
              afterBound afterOwned h)
          | returned result memory =>
            cases hr : result.mapM (checkedValue (leaveFrame frame memory)) <;>
              simp only [run, hb, ho, hs, hr, Except.mapError, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
            · cases h
            · cases h
              exact first.trans ⟨by rw [leaveFrame_nextIdentity]; exact Nat.le_refl _,
                fun id old => leaveFrame_preserves_older_allocations _ _ _ owned id old⟩
          | call callee arguments rest memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have fresh := enterFrame_fresh _ _ _ _ _ he
                have childBound := Nat.le_trans afterBound fresh.1.next
                have childOwned : childFrame.OwnedAbove watermark :=
                  fun id member => Nat.le_trans afterBound (fresh.2 id member).1
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  have childPreserves := ih callee 0 arguments childFrame [] childMemory memory' result
                    childBound childOwned hr
                  have prior := (first.trans (fresh.1.below watermark afterBound)).trans childPreserves
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  exact prior.trans (ih method (pc + 1) args frame (result ++ rest) memory' final values
                    (Nat.le_trans bound prior.next) owned h)
          | construct callee arguments rest frame' temporary memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault => simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have fresh := enterFrame_fresh _ _ _ _ _ he
                have childBound := Nat.le_trans afterBound fresh.1.next
                have childOwned : childFrame.OwnedAbove watermark :=
                  fun id member => Nat.le_trans afterBound (fresh.2 id member).1
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨memory', result⟩ := returned
                  have childPreserves := ih callee 0 arguments childFrame [] childMemory memory' result
                    childBound childOwned hr
                  have prior := (first.trans (fresh.1.below watermark afterBound)).trans childPreserves
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                  split at h
                  · cases h
                  · cases hl : loadValue memory' (.address temporary) (localWidth .vector256) <;>
                      simp only [hl] at h
                    · cases h
                    · rename_i value
                      exact prior.trans (ih method (pc + 1) args frame' (.scalar value :: rest) memory'
                        final values (Nat.le_trans bound prior.next) afterOwned h)

/-- A child may mutate caller bytes, but cannot expire or replace caller storage. -/
theorem entered_run_preserves_caller_allocations (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (args values : List Value) (frame : Frame) (m entered final : Memory)
    (setup : enterFrame body args m = .ok (frame, entered))
    (finish : run program fuel method 0 args frame [] entered = .ok (final, values)) :
    AllocationExtension m final := by
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have preserved := run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ m.nextIdentity
    fresh.1.next (fun id member => (fresh.2 id member).1) finish
  exact ⟨Nat.le_trans fresh.1.next preserved.next,
    fun id old => (preserved.lookup id old).trans (fresh.1.lookup id old)⟩

theorem invoke_preserves_caller_allocations (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory)
    (h : invoke program fuel method args m = .ok (final, values)) :
    AllocationExtension m final := by
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
        exact entered_run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ he h

theorem invoke_preserves_caller_reference (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (r formed : Reference) (hm : m.WellFormed)
    (valid : form m r = .ok formed)
    (h : invoke program fuel method args m = .ok (final, values)) :
    form final r = .ok formed :=
  (invoke_preserves_caller_allocations _ _ _ _ _ _ _ h).preserves_reference hm r formed valid

theorem programStep_extends_allocations {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : ProgramStep program method pc args frame stack m action) :
    AllocationExtension m action.memory := by
  obtain ⟨body, op, _, _, h⟩ := h
  exact step_extends_allocations _ _ _ _ _ _ _ _ h

theorem programStep_ownedAbove {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    {watermark : Nat} (h : ProgramStep program method pc args frame stack m action)
    (bound : watermark ≤ m.nextIdentity) (owned : frame.OwnedAbove watermark) :
    action.OwnedAbove watermark := by
  obtain ⟨body, op, _, _, h⟩ := h
  exact step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound h

/-- Caller lifetimes are preserved even at prefixes of runs which later fault.
    Each observation uses actual fetched steps and actual nested execution. -/
theorem runVisits_preserves_caller_allocations {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed)
    (watermark : Nat) (bound : watermark ≤ m.nextIdentity) (owned : frame.OwnedAbove watermark) :
    AllocationsBelow m observed watermark := by
  induction visit with
  | initial => exact (AllocationExtension.refl _).below watermark bound
  | stepped step => exact (programStep_extends_allocations step).below watermark bound
  | next step later ih =>
    have first := programStep_extends_allocations step
    exact (first.below watermark bound).trans
      (ih (Nat.le_trans bound first.next) (programStep_ownedAbove step bound owned))
  | entered step call lookup enter =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    exact (first.trans fresh.1).below watermark bound
  | child step call lookup enter later ih =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have prior := first.trans fresh.1
    exact (prior.below watermark bound).trans
      (ih (Nat.le_trans bound prior.next)
        (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1))
  | callContinue step lookup enter finish later ih =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ watermark
      (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1) finish
    have prior := (setup.below watermark bound).trans child
    exact prior.trans (ih (Nat.le_trans bound prior.next) owned)
  | constructContinue step lookup enter finish load later ih =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ watermark
      (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1) finish
    have prior := (setup.below watermark bound).trans child
    exact prior.trans (ih (Nat.le_trans bound prior.next) (programStep_ownedAbove step bound owned))
  | expired step =>
    have first := (programStep_extends_allocations step).below watermark bound
    exact first.trans ⟨by rw [leaveFrame_nextIdentity]; exact Nat.le_refl _,
      fun id old => leaveFrame_preserves_older_allocations _ _ _ owned id old⟩

theorem runVisits_preserves_caller_reference {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed)
    (watermark : Nat) (bound : watermark ≤ m.nextIdentity) (owned : frame.OwnedAbove watermark)
    (r formed : Reference) (old : r.allocation < watermark) (valid : form m r = .ok formed) :
    form observed r = .ok formed :=
  (runVisits_preserves_caller_allocations visit watermark bound owned).preserves_reference r formed old valid

#print axioms run_preserves_caller_allocations
#print axioms invoke_preserves_caller_allocations
#print axioms invoke_preserves_caller_reference
#print axioms runVisits_preserves_caller_allocations
#print axioms runVisits_preserves_caller_reference

end CIL.Safety
