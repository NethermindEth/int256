import UInt256.Methods.Subtract.ScalarSmallChecked
import UInt256.Safety.ReportingContract

/-! The extracted SubtractImpl with AVX2 disabled skips its vector block and forwards the
    scalar helper's difference and underflow flag. -/

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- The scalar fallback is the final call before return; the fetched target is
    checked below against the independently discovered scalar helper. -/
def dispatchCall : Nat := Extracted.subtractVector256Body.code.length - 2

theorem dispatch_contract_of_scalar
    (scalarChecked : ∀ memory left right output,
      CallingConditions Extracted.program memory [left, right] [output] →
      ∃ fuel final values,
        invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
          .ok (final, values) ∧ SubtractResult memory final values left right output) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat))
      Extracted.program Extracted.subtractVector256Index := by
  intro memory left right output call
  let post := fun final returned => SubtractResult memory final returned left right output
  have found : Extracted.program[Extracted.subtractVector256Index]? =
      some Extracted.subtractVector256Body := by rfl
  have fits : FrameSetupFits Extracted.subtractVector256Body
      (binaryArguments left right output) := by
    simp [cil_code, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit,
      ParameterArgumentsFit]
  obtain ⟨frame, entered, setup, _⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, values, invoked, result⟩ :=
    scalarChecked entered left right output enteredCall
  obtain rfl := result.flag
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have fetched : Extracted.subtractVector256Body.code[dispatchCall]? =
      some (.call scalarIndex 3) := by
    conv in dispatchCall => cbv
    simp only [cil_code]
    rfl
  have returned : Extracted.subtractVector256Body.code[dispatchCall + 1]? =
      some (.ret (some .unsigned8)) := by
    conv in dispatchCall => cbv
    simp only [Nat.reduceAdd, cil_code]
  have forwarded := run_call_post (post := post) found (pc := dispatchCall)
    (args := binaryArguments left right output) fetched
    (step_call_loaded enteredCall.binary_arguments_valid rfl) ⟨childFuel, invoked⟩
    (run_return_exists found returned
      (step_return_unchanged (narrow := some .unsigned8) rfl rfl rfl
        ⟨_, rfl, CIL.NarrowKind.extend_ite_one_zero _ _⟩) rfl
      (Profile.subtract_result_retire call
        (enterFrame_preserves_caller_memory _ _ _ _ _ setup).cells
        fresh.1.next (fun id member => (fresh.2 id member).1) result))
  have executed : ∃ fuel final returned,
      run Extracted.program fuel Extracted.subtractVector256Index 0
        (binaryArguments left right output) frame [] entered = .ok (final, returned) ∧
      post final returned := by
    conv at forwarded in dispatchCall => cbv
    cil_contract_steps [found, binaryArguments,
      enteredCall.input_formed (reference := left) (by simp),
      enteredCall.input_formed (reference := right) (by simp),
      enteredCall.output_formed (reference := output) (by simp)] until forwarded
  obtain ⟨fuel, final, returned, ran, retired⟩ := executed
  obtain rfl := retired.flag
  refine ⟨fuel, final, ?_, retired.value, retired.writable, retired.footprint⟩
  simpa only [subtractUnderflow, decide_eq_true_eq] using
    InvocationCertificate.of_invoke call.1.wellFormed call.2
      (invoke_of_run found (checkedValues_of_valid call.binary_arguments_valid) setup ran)

end UInt256Proof.Subtract.Safety
