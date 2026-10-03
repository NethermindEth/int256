import CIL.Semantics

namespace CIL

-- Increasing fuel preserves every successful execution, including nested calls.

theorem run_mono (program : Program) (fuel extra method pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (result : Memory × List Value)
    (h : run program fuel method pc args frame stack memory = some result) :
    run program (fuel + extra) method pc args frame stack memory = some result := by
  induction fuel generalizing method pc args frame stack memory result with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hbody : program[method]? with
    | none => simp [run, hbody] at h
    | some body =>
      cases hop : body.code[pc]? with
      | none => simp [run, hbody, hop] at h
      | some op =>
        cases hstep : step op body.returnsValue pc args frame stack memory body.profile with
        | none => simp [run, hbody, hop, hstep] at h
        | some action =>
          cases action with
          | next target stack' memory' =>
            simp [run, hbody, hop, hstep] at h
            simpa [Nat.succ_add, run, hbody, hop, hstep] using
              ih method target args frame stack' memory' result h
          | returned values final =>
            simp [run, hbody, hop, hstep] at h
            simpa [Nat.succ_add, run, hbody, hop, hstep] using h
          | call callee args' rest memory' =>
            cases hchild : program[callee]? with
            | none => simp [run, hbody, hop, hstep, hchild] at h
            | some child =>
              cases hrun : run program fuel callee 0 args' (frame + 1) []
                  (initFrame memory' (frame + 1) child args') with
              | none => simp [run, hbody, hop, hstep, hchild, hrun] at h
              | some childResult =>
                obtain ⟨final, values⟩ := childResult
                have hc := ih callee 0 args' (frame + 1) []
                  (initFrame memory' (frame + 1) child args') (final, values) hrun
                simp [run, hbody, hop, hstep, hchild, hrun] at h
                have hp := ih method (pc + 1) args frame (values ++ rest) final result h
                simpa [Nat.succ_add, run, hbody, hop, hstep, hchild, hc] using hp
          | construct callee args' rest memory' =>
            cases hchild : program[callee]? with
            | none => simp [run, hbody, hop, hstep, hchild] at h
            | some child =>
              cases hrun : run program fuel callee 0 args' (frame + 1) []
                  (initFrame memory' (frame + 1) child args') with
              | none => simp [run, hbody, hop, hstep, hchild, hrun] at h
              | some childResult =>
                obtain ⟨final, values⟩ := childResult
                have hc := ih callee 0 args' (frame + 1) []
                  (initFrame memory' (frame + 1) child args') (final, values) hrun
                cases values with
                | cons value tail => simp [run, hbody, hop, hstep, hchild, hrun] at h
                | nil =>
                  cases hsnapshot : readAggregate final frame 2 pc with
                  | none => simp [run, hbody, hop, hstep, hchild, hrun, hsnapshot] at h
                  | some value =>
                    simp [run, hbody, hop, hstep, hchild, hrun, hsnapshot] at h
                    have hp := ih method (pc + 1) args frame (value :: rest) final result h
                    simpa [Nat.succ_add, run, hbody, hop, hstep, hchild, hc, hsnapshot] using hp

theorem run_of_le (program : Program) (fuel larger method pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (result : Memory × List Value) (hf : fuel ≤ larger)
    (h : run program fuel method pc args frame stack memory = some result) :
    run program larger method pc args frame stack memory = some result := by
  have he : fuel + (larger - fuel) = larger := by omega
  simpa only [he] using run_mono program fuel (larger - fuel) method pc args frame stack memory result h

-- Any two successful finite executions have the same observable result.
theorem run_result_unique (program : Program) (first second method pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (a b : Memory × List Value)
    (ha : run program first method pc args frame stack memory = some a)
    (hb : run program second method pc args frame stack memory = some b) : a = b := by
  have hmaxa := run_of_le program first (max first second) method pc args frame stack memory a
    (Nat.le_max_left _ _) ha
  have hmaxb := run_of_le program second (max first second) method pc args frame stack memory b
    (Nat.le_max_right _ _) hb
  exact Option.some.inj (hmaxa.symm.trans hmaxb)

theorem invoke_result_unique (program : Program) (first second method : Nat)
    (args : List Value) (memory : Memory) (a b : Memory × List Value)
    (ha : invoke program first method args memory = some a)
    (hb : invoke program second method args memory = some b) : a = b := by
  cases hbody : program[method]? with
  | none => simp [invoke, hbody] at ha
  | some body =>
    simp only [invoke, hbody] at ha hb
    exact run_result_unique _ _ _ _ _ _ _ _ _ _ _ ha hb

end CIL
