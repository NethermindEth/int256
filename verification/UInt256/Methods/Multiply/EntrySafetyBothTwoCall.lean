import UInt256.Methods.Multiply.EntrySafetyArithmetic
import UInt256.Methods.Multiply.BothTwoSafety
import UInt256.Safety.OutputCallReturn

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_both_two_branch (word : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (leftUpper : inputUpper original left = 0) (rightUpper : inputUpper original right = 0) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 64 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 3
    apply run_next_exists post found (by rfl)
    simp [step, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  have leftZero : inputLimb current left 2 = 0 ∧ inputLimb current left 3 = 0 := by
    simpa only [state.input_limb originalCall left (by simp)] using input_upper_zero original left leftUpper
  have rightZero : inputLimb current right 2 = 0 ∧ inputLimb current right 3 = 0 := by
    simpa only [state.input_limb originalCall right (by simp)] using input_upper_zero original right rightUpper
  obtain ⟨childFuel, childFinal, invoked, result⟩ := both_two_invoke word current left right output state.call leftZero rightZero
  have leftValue := state.input_value originalCall left (by simp)
  have rightValue := state.input_value originalCall right (by simp)
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    simpa only [ProductResult, leftValue, rightValue] using result
  apply run_output_call (callee := bothTwoIndex) (callArgs := productArgs left right output)
    state originalCall owned (inputValue original left * inputValue original right)
    found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
  simp [step, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

#print axioms multiply_both_two_branch
end UInt256Proof.Multiply.Safety
