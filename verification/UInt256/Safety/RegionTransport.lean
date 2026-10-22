import CIL.Safety.Embedding.Step
import CIL.Safety.Linking

namespace UInt256Proof.Transport
open CIL.Safety

/-- Every target of a successful next-pc action lies in the region; calls enter it at pc 0 and resume adjacent. -/
def closedAction (region : Nat → Nat → Prop) (pcMap : Nat → Nat → Nat)
    (method pc : Nat) : FrameAction → Prop
  | .next target _ _ _ => region method target
  | .call callee _ _ _ => region callee 0 ∧ pcMap callee 0 = 0 ∧
      region method (pc + 1) ∧ pcMap method (pc + 1) = pcMap method pc + 1
  | .returned _ _ => True
  | .construct .. => False

structure Correspondence (source target : CIL.Program) (region : Nat → Nat → Prop)
    (pcMap : Nat → Nat → Nat) : Prop where
  frames : ∀ (method : Nat) (body : CIL.Method), source[method]? = some body → ∃ targetBody,
    target[method]? = some targetBody ∧ ∀ args memory, enterFrame targetBody args memory = enterFrame body args memory
  steps : ∀ method pc body op args frame stack memory action,
    region method pc → source[method]? = some body → body.code[pc]? = some op →
    step body op pc args frame stack memory = .ok action →
    ∃ targetBody targetOp, target[method]? = some targetBody ∧
      targetBody.code[pcMap method pc]? = some targetOp ∧
      step targetBody targetOp (pcMap method pc) args frame stack memory = .ok (action.relabel (pcMap method)) ∧
      closedAction region pcMap method pc action

theorem run_success_transport (source target : CIL.Program) (region : Nat → Nat → Prop)
    (pcMap : Nat → Nat → Nat) (relation : Correspondence source target region pcMap)
    (fuel method pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value) (inside : region method pc)
    (finished : run source fuel method pc args frame stack memory = .ok (final, values)) :
    run target fuel method (pcMap method pc) args frame stack memory = .ok (final, values) := by
  induction fuel generalizing method pc args frame stack memory final values with
  | zero => simp [run] at finished
  | succ fuel ih =>
    cases hb : source[method]? with
    | none => simp [run, hb] at finished
    | some body =>
      cases ho : body.code[pc]? with
      | none => simp [run, hb, ho] at finished
      | some op =>
        cases hs : step body op pc args frame stack memory with
        | error fault => simp [run, hb, ho, hs, Bind.bind, Except.bind, Except.mapError] at finished
        | ok action =>
          obtain ⟨targetBody, targetOp, tb, to, ts, closed⟩ := relation.steps _ _ _ _ _ _ _ _ _ inside hb ho hs
          cases action with
          | next nextPC nextStack nextFrame updated =>
            simp only [closedAction] at closed
            simp only [run, hb, ho, hs, Bind.bind, Except.bind, Except.mapError] at finished
            simpa only [run, tb, to, ts, FrameAction.relabel, Bind.bind, Except.bind, Except.mapError, Pure.pure,
              Except.pure] using ih method nextPC args nextFrame nextStack updated final values closed finished
          | returned returned updated =>
            cases hc : returned.mapM (checkedValue (leaveFrame frame updated)) with
            | error fault => simp [run, hb, ho, hs, hc, Bind.bind, Except.bind, Except.mapError] at finished
            | ok checked =>
              simpa only [run, tb, to, ts, FrameAction.relabel, hc, Bind.bind, Except.bind, Except.mapError, Pure.pure,
                Except.pure] using
                (show (Except.ok (leaveFrame frame updated, checked) : Except LocatedFault _) = .ok (final, values) from by
                  simpa only [run, hb, ho, hs, hc, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] using finished)
          | construct callee arguments rest nextFrame temporary kind updated => exact False.elim closed
          | call callee arguments rest updated =>
            obtain ⟨childRegion, childPC, parentRegion, parentPC⟩ := closed
            cases ch : source[callee]? with
            | none => simp [run, hb, ho, hs, ch, Bind.bind, Except.bind, Except.mapError] at finished
            | some childBody =>
              obtain ⟨targetChild, tch, setup⟩ := relation.frames _ _ ch
              cases he : enterFrame childBody arguments updated with
              | error fault => simp [run, hb, ho, hs, ch, he, Bind.bind, Except.bind, Except.mapError] at finished
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases childRun : run source fuel callee 0 arguments childFrame [] childMemory with
                | error fault => simp [run, hb, ho, hs, ch, he, childRun, Bind.bind, Except.bind, Except.mapError] at finished
                | ok outcome =>
                  obtain ⟨childFinal, childValues⟩ := outcome
                  have childTransport := ih callee 0 arguments childFrame [] childMemory childFinal childValues childRegion childRun
                  rw [childPC] at childTransport
                  simp only [run, hb, ho, hs, ch, he, childRun, Bind.bind, Except.bind, Except.mapError] at finished
                  have parentTransport := ih method (pc + 1) args frame (childValues ++ rest) childFinal final values parentRegion finished
                  rw [parentPC] at parentTransport
                  simpa only [run, tb, to, ts, FrameAction.relabel, tch, setup, he, childTransport,
                    Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] using parentTransport

/-- Renames the four branch kinds the shift bodies use; the helper variant's suffix is stated with it. -/
def relocateOp (f : Nat → Nat) : CIL.Op → CIL.Op
  | .bge target => .bge (f target)
  | .bltu target => .bltu (f target)
  | .bne target => .bne (f target)
  | .brnonzero target => .brnonzero (f target)
  | op => op

def FlowResult (lower : Nat) (calleeAllowed : Nat → Prop) : FrameAction → Prop
  | .next pc _ _ _ => lower ≤ pc
  | .call callee _ _ _ => calleeAllowed callee
  | .returned _ _ => True
  | .construct .. => False

/-- Code targets stay at or above `lower`, calls name allowed callees, and nothing constructs. -/
def FlowInput (lower : Nat) (calleeAllowed : Nat → Prop) : CIL.Op → Prop
  | .call callee _ => calleeAllowed callee
  | .newVector256 .. | .newAggregate .. => False
  | op => ∀ target ∈ op.targets, lower ≤ target

theorem relabel_fixed (r : Nat → Nat) (op : CIL.Op) (fixed : ∀ target ∈ op.targets, r target = target) :
    op.relabel r = op := by
  induction op <;> simp_all [CIL.Op.relabel, CIL.Op.targets]
  exact (List.map_congr_left fixed).trans (List.map_id _)

/-- A successful next-pc step resumes at the fallthrough of a continuing instruction or at one of its targets. -/
theorem step_next_target {body : CIL.Method} {op : CIL.Op} {pc : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {memory : Memory} {target : Nat} {stack' : List Value} {frame' : Frame} {memory' : Memory}
    (executed : step body op pc args frame stack memory = .ok (.next target stack' frame' memory')) :
    (op.continues = true ∧ target = pc + 1) ∨ target ∈ op.targets := by
  refine Decidable.byContradiction fun outside => ?_
  let r : Nat → Nat := fun t => if t = target then target + 1 else t
  have same : op.relabel r = op := relabel_fixed r op fun t member =>
    ite_eq_right fun e => outside (.inr (by rw [← e]; exact member))
  have moved := step_relabel op body body r pc pc args frame stack memory _
    ⟨rfl, rfl, rfl, fun continues => ite_eq_right fun e => outside (.inl ⟨continues, e.symm⟩)⟩ executed
  rw [same, executed] at moved
  have shifted : target = r target := by
    simp only [FrameAction.relabel, Except.ok.injEq, FrameAction.next.injEq] at moved
    exact moved.1
  have : r target = target + 1 := ite_eq_left rfl
  omega

theorem step_call_action {body : CIL.Method} {callee argc pc : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {memory : Memory} {action : FrameAction}
    (executed : step body (.call callee argc) pc args frame stack memory = .ok action) :
    ∃ arguments rest updated, action = .call callee arguments rest updated := by
  unfold step at executed
  split at executed
  · cases executed
  · obtain ⟨_, _, executed⟩ := except_bind_ok executed
    cases executed
    exact ⟨_, _, _, rfl⟩

theorem step_flow (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (memory : Memory) (action : FrameAction) (lower : Nat) (calleeAllowed : Nat → Prop)
    (successor : lower ≤ pc + 1) (targets : FlowInput lower calleeAllowed op)
    (executed : step body op pc args frame stack memory = .ok action) : FlowResult lower calleeAllowed action := by
  have callee := step_callee executed
  cases op
  case call method argc =>
    obtain ⟨_, _, _, rfl⟩ := step_call_action executed
    exact targets
  case newVector256 | newAggregate => exact targets.elim
  all_goals
    cases action with
    | next target _ _ _ =>
      rcases step_next_target executed with ⟨_, rfl⟩ | member
      · exact successor
      · exact targets target member
    | returned => trivial
    | call | construct => simp [FrameAction.callee, CIL.Op.callees] at callee

#print axioms run_success_transport
#print axioms step_flow
end UInt256Proof.Transport
