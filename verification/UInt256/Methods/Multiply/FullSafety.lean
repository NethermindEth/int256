import UInt256.Methods.Multiply.FullSafetyOutput
import UInt256.Methods.Multiply.FullSafetyTopContract

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem full_invoke (contract : WordContract) (top : FullTopContract) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel fullIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := full_frame_setup memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run Extracted.program fuel fullIndex 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply full_inputs memory entered entered left right output frame call enteredWF homes state post
    intro m0 state0
    apply top memory entered m0 left right output frame call enteredWF homes state0 post
    intro m1 state1
    apply full_second_column contract memory entered m1 left right output frame call enteredWF homes state1 post
    intro m2 state2
    apply full_middle_column memory entered m2 left right output frame call enteredWF homes state2 post
    intro m3 state3
    apply full_first_upper contract memory entered m3 left right output frame call enteredWF homes state3 post
    intro m4 state4
    apply full_upper contract memory entered m4 left right output frame call enteredWF homes state4 post
    intro m5 state5
    apply full_final contract memory entered m5 left right output frame call enteredWF homes state5 post
    intro m6 state6
    exact full_output memory entered m6 left right output frame call owned state6
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns := result.returns
  subst returned
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

#print axioms full_invoke
end UInt256Proof.Multiply.Safety
