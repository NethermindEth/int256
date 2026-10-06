import UInt256.Methods.Multiply.BothTwoSafetyOutput

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem both_two_invoke (contract : WordContract) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (leftUpper : inputLimb memory left 2 = 0 ∧ inputLimb memory left 3 = 0)
    (rightUpper : inputLimb memory right 2 = 0 ∧ inputLimb memory right 3 = 0) :
    ∃ fuel final,
      invoke Extracted.program fuel bothTwoIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := both_two_frame_setup memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply both_two_inputs memory entered entered left right output frame call enteredWF homes state post
    intro m0 state0
    apply both_two_first_products contract memory entered m0 left right output frame call enteredWF homes state0 post
    intro m1 state1
    apply both_two_second_column contract memory entered m1 left right output frame call enteredWF homes state1 post
    intro m2 state2
    apply both_two_final_column contract memory entered m2 left right output frame call enteredWF homes state2 post
    intro m3 state3
    exact both_two_output memory entered m3 left right output frame call owned state3 leftUpper rightUpper
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns := result.returns
  subst returned
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

#print axioms both_two_invoke
end UInt256Proof.Multiply.Safety
