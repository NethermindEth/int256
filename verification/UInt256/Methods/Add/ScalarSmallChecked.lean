import UInt256.Methods.Add.ScalarSmallFacts

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem scalar_right_small_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (small : inputLimb memory right 1 ||| inputLimb memory right 2 ||| inputLimb memory right 3 = 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ AddResult memory final values left right output := by
  let post := fun final values => AddResult memory final values left right output
  obtain ⟨frame, entered, setup, homes, _, enteredWF⟩ :=
    scalar_frame_setup memory (scalarArguments left right output) call.1.1
  have executed := scalar_right_prefix_checked memory entered left right output [.scalar (.i32 0)]
    frame call setup homes post (by
      intro home current slot loaded preserved currentCall authority
      rw [small]
      apply scalar_small_prefix false left right output home (inputLimb memory right 0) frame current
        (currentCall.input_formed (by simp [scalarSmallSource])) (currentCall.output_formed (by simp)) slot loaded post
      have next := scalar_private_next memory entered current frame homes enteredWF currentCall.1.1 authority
      have math := scalar_small_values false memory current left right output call preserved small
      exact scalar_small_finish false memory entered current frame left right output (inputLimb memory right 0)
        call setup currentCall preserved next math.1 math.2)
  obtain ⟨fuel, final, values, finished, result⟩ := executed
  have checked : (scalarArguments left right output).mapM (checkedValue memory) =
      .ok (scalarArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [scalarArguments, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, values, ?_, result⟩
  change run Extracted.program fuel Extracted.addScalarIndex 0
    (scalarArguments left right output) frame [] entered = .ok (final, values) at finished
  simp only [cil_code] at setup
  simpa only [invoke, cil_code, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished

theorem scalar_left_small_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (small : inputLimb memory left 1 ||| inputLimb memory left 2 ||| inputLimb memory left 3 = 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ AddResult memory final values left right output := by
  let post := fun final values => AddResult memory final values left right output
  apply scalar_large_right_prefix memory left right output call largeRight post
  intro frame entered rightHome leftHome current setup homes ready
  rw [small]
  apply scalar_small_prefix true left right output leftHome (inputLimb memory left 0) frame current
    (ready.call.input_formed (by simp [scalarSmallSource])) (ready.call.output_formed (by simp)) ready.leftSlot ready.leftRead post
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have next := scalar_private_next memory entered current frame homes enteredWF ready.call.1.1 ready.authority
  have math := scalar_small_values true memory current left right output call ready.preserved small
  exact scalar_small_finish true memory entered current frame left right output (inputLimb memory left 0)
    call setup ready.call ready.preserved next math.1 math.2

#print axioms scalar_right_small_checked
#print axioms scalar_left_small_checked

end UInt256Proof.Safety
