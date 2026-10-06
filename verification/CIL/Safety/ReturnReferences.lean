import CIL.Safety.LiveValues

namespace CIL.Safety

theorem checkedValues_mapError_valid (m : Memory) (values result : List Value)
    (locate : ExecutionFault → α)
    (h : (values.mapM (checkedValue m)).mapError locate = .ok result) : ValuesValid m result := by
  cases hc : values.mapM (checkedValue m) <;> simp only [hc, Except.mapError] at h
  · cases h
  · cases h
    exact (checkedValues_valid _ _ _ hc).2

/-- Normal results have passed the reference check after frame expiration.
    This includes results returning through arbitrary nested call chains. -/
theorem run_result_valid (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ValuesValid final values := by
  induction fuel generalizing method pc args frame stack m final values with
  | zero => cases h
  | succ fuel ih =>
    simp only [run] at h
    repeat' first
      | solve | apply ih; assumption
      | solve | exact (checkedValues_valid _ _ _ (by assumption)).2
      | solve | apply checkedValues_mapError_valid; assumption
      | cases h
      | split at h
      | simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem invoke_result_valid (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory)
    (h : invoke program fuel method args m = .ok (final, values)) : ValuesValid final values := by
  unfold invoke at h
  repeat' first
    | solve | apply run_result_valid; assumption
    | cases h
    | split at h
    | simp only [Except.mapError, Bind.bind, Except.bind] at h

#print axioms run_result_valid
#print axioms invoke_result_valid

end CIL.Safety
