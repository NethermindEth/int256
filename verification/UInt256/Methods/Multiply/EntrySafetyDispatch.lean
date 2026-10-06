import UInt256.Methods.Multiply.EntrySafetyLargeDispatch
import UInt256.Methods.Multiply.EntrySafetySmall
import UInt256.Methods.Multiply.EntrySafetyScalarCall
import CIL.Safety.ScalarBranch

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_dispatch (word : WordContract) (top : FullTopContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right)) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 28 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have loadLeft := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 4) (inputTail original left) (by rfl)
  have loadRight := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 5) (inputTail original right) (by rfl)
  apply run_next_exists post found (by rfl) (loadLeft _ _)
  apply run_next_exists post found (by rfl) (loadRight _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, numericValue, scalars, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
  by_cases both : inputTail original left ||| inputTail original right = 0
  · simp only [both, ite_true]
    have halves := BitVec.or_eq_zero_iff.mp both
    exact multiply_small_branch word original entered current left right output frame originalCall enteredWF homes owned state halves.1 halves.2
  · simp only [both, ite_false]
    apply run_next_exists post found (by rfl) (loadRight _ _)
    apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
    by_cases rightZero : inputTail original right = 0
    · simp only [rightZero, ite_true]
      exact multiply_scalar_branch word false original entered current left right output frame originalCall owned state rightZero
    · simp only [rightZero, ite_false]
      apply run_next_exists post found (by rfl) (loadLeft _ _)
      apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
      by_cases leftZero : inputTail original left = 0
      · simp only [leftZero, ite_true]
        exact multiply_scalar_branch word true original entered current left right output frame originalCall owned state leftZero
      · simp only [leftZero, ite_false]
        exact multiply_large_dispatch word top original entered current left right output frame originalCall owned state

#print axioms multiply_dispatch
end UInt256Proof.Multiply.Safety
