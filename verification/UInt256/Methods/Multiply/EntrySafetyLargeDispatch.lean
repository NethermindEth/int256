import UInt256.Methods.Multiply.EntrySafetyArithmetic
import UInt256.Methods.Multiply.LeftTwoSafety
import UInt256.Safety.OutputCallReturn
import UInt256.Safety.ReadOnlyForwarder
import UInt256.Methods.Multiply.BothTwoSafety
import UInt256.Methods.Multiply.FullSafety
import CIL.Safety.ScalarBranch

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

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_full_branch (word : WordContract) (top : FullTopContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right)) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 83 (productArgs left right output) frame [] current =
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
  obtain ⟨childFuel, childFinal, invoked, result⟩ := full_invoke word top current left right output state.call
  have leftValue := state.input_value originalCall left (by simp)
  have rightValue := state.input_value originalCall right (by simp)
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    simpa only [ProductResult, leftValue, rightValue] using result
  apply run_output_call (callee := fullIndex) (callArgs := productArgs left right output)
    state originalCall owned (inputValue original left * inputValue original right)
    found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
  simp [step, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

#print axioms multiply_full_branch
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_large_dispatch (word : WordContract) (top : FullTopContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right)) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 60 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have loadLeft := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 2) (inputUpper original left) (by rfl)
  have loadRight := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 3) (inputUpper original right) (by rfl)
  apply run_next_exists post found (by rfl) (loadLeft _ _)
  apply run_next_exists post found (by rfl) (loadRight _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, numericValue, scalars, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
  by_cases both : inputUpper original left ||| inputUpper original right = 0
  · simp only [both, ite_true]
    have halves := BitVec.or_eq_zero_iff.mp both
    exact multiply_both_two_branch word original entered current left right output frame originalCall owned state halves.1 halves.2
  · simp only [both, ite_false]
    apply run_next_exists post found (by rfl) (loadLeft _ _)
    apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
    by_cases leftZero : inputUpper original left = 0
    · simp only [leftZero, ite_true]
      exact multiply_left_two_branch word false original entered current left right output frame originalCall owned state leftZero
    · simp only [leftZero, ite_false]
      apply run_next_exists post found (by rfl) (loadRight _ _)
      apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
      by_cases rightZero : inputUpper original right = 0
      · simp only [rightZero, ite_true]
        exact multiply_left_two_branch word true original entered current left right output frame originalCall owned state rightZero
      · simp only [rightZero, ite_false]
        exact multiply_full_branch word top original entered current left right output frame originalCall owned state

#print axioms multiply_large_dispatch
end UInt256Proof.Multiply.Safety
