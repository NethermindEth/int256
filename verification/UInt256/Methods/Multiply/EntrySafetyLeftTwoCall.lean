import UInt256.Methods.Multiply.EntrySafetyArithmetic
import UInt256.Methods.Multiply.LeftTwoSafety
import UInt256.Safety.OutputCallReturn
import UInt256.Safety.ReadOnlyForwarder

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_left_two_branch (word : WordContract) (swapped : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (upper : inputUpper original (if swapped then right else left) = 0) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex (if swapped then 78 else 71)
        (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let firstInput := if swapped then right else left
  let secondInput := if swapped then left else right
  have firstMember : firstInput ∈ [left, right] := by cases swapped <;> simp [firstInput]
  have secondMember : secondInput ∈ [left, right] := by cases swapped <;> simp [secondInput]
  have call : CallingConditions Extracted.program current [firstInput, secondInput] [output] := by
    cases swapped
    · exact state.call
    · exact state.call.swap_binary_inputs
  have zero : inputLimb current firstInput 2 = 0 ∧ inputLimb current firstInput 3 = 0 := by
    simpa only [state.input_limb originalCall firstInput firstMember] using
      input_upper_zero original firstInput upper
  obtain ⟨childFuel, childFinal, invoked, result⟩ := left_two_invoke word current firstInput secondInput output call zero
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    have firstValue := state.input_value originalCall firstInput firstMember
    have secondValue := state.input_value originalCall secondInput secondMember
    change OutputResult current childFinal output
      (inputValue current firstInput * inputValue current secondInput) [] at result
    rw [firstValue, secondValue] at result
    cases swapped
    · exact result
    · simpa only [firstInput, secondInput, ite_true, BitVec.mul_comm] using result
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  cases swapped <;> dsimp [firstInput, secondInput] at invoked ⊢
  all_goals
    iterate 3
      apply run_next_exists post found (by rfl)
      simp [step, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_output_call (callee := leftTwoIndex)
      state originalCall owned (inputValue original left * inputValue original right)
      found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
    simp [step, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

#print axioms multiply_left_two_branch
end UInt256Proof.Multiply.Safety
