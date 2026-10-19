import CIL.Safety.Execution

namespace UInt256Proof.Transport
open CIL.Safety


def relocateAction (pcMap : Nat → Nat → Nat) (method : Nat) : FrameAction → FrameAction
  | .next target stack frame memory => .next (pcMap method target) stack frame memory
  | other => other

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
      step targetBody targetOp (pcMap method pc) args frame stack memory = .ok (relocateAction pcMap method action) ∧
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
            simpa only [run, tb, to, ts, relocateAction, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] using
              ih method nextPC args nextFrame nextStack updated final values closed finished
          | returned returned updated =>
            cases hc : returned.mapM (checkedValue (leaveFrame frame updated)) with
            | error fault => simp [run, hb, ho, hs, hc, Bind.bind, Except.bind, Except.mapError] at finished
            | ok checked =>
              simpa only [run, tb, to, ts, relocateAction, hc, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] using
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
                  simpa only [run, tb, to, ts, relocateAction, tch, setup, he, childTransport,
                    Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] using parentTransport


#print axioms run_success_transport
end UInt256Proof.Transport
