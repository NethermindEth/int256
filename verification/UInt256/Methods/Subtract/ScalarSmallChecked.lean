import UInt256.Methods.Subtract.ScalarSafetyPrefix
import UInt256.Methods.Subtract.SmallHelper
import UInt256.Methods.Subtract.SafetyResult
import CIL.Safety.Forwarders

/-! The small-right route of the extracted scalar body calls the checked small-word helper on
    the left operand and the saved right low limb. -/

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

def scalarSmallCall : Nat := scalarBody.code.findIdx fun op => match op with
  | .call callee _ => callee == Extracted.subtractScalarUInt64Index | _ => false

/-- A right operand of one limb takes the small helper; its result retires the private frame
    with the full difference, the exact underflow flag and the caller bytes kept. -/
theorem scalar_right_small_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (small : inputLimb memory right 1 ||| inputLimb memory right 2 ||| inputLimb memory right 3 = 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ SubtractResult memory final values left right output := by
  let post := fun final values => SubtractResult memory final values left right output
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    scalar_frame_setup memory (binaryArguments left right output) call.1.1
  obtain ⟨fuel, final, values, finished, result⟩ := scalar_right_prefix_checked memory entered
    left right output frame call setup homes post (by
      intro home current slot loaded preserved currentCall authority next
      rw [small]
      obtain ⟨childFuel, after, values, certified, result⟩ :=
        Profile.small_checked Extracted.program Extracted.subtractScalarUInt64Index
          Extracted.storeLimbsIndex Extracted.profile (by rfl) (by rfl) current left output
          (inputLimb memory right 0)
          ⟨currentCall.1.mono (by simp) (fun _ member => member), currentCall.2⟩
      obtain rfl := result.underflow
      have keptRight : inputValue current right = inputValue memory right := by
        simp only [inputValue,
          call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
      have fl := currentCall.input_formed (reference := left) (by simp)
      have fo := currentCall.output_formed (reference := output) (by simp)
      have finish : ∃ fuel final returned,
          run Extracted.program fuel scalarIndex scalarSmallCall
            (binaryArguments left right output) frame
            [.reference (.address output), .scalar (.i64 (inputLimb memory right 0)),
              .reference (.address left)] current = .ok (final, returned) ∧
            post final returned :=
        run_call_post found (by rfl) (by cil_checked_step [Profile.smallArguments, fl, fo])
          ⟨childFuel, certified.1⟩
          (run_return_exists found (by rfl)
            (step_return_unchanged (narrow := some .unsigned8) rfl rfl rfl
              ⟨_, rfl, CIL.NarrowKind.extend_ite_one_zero _ _⟩) rfl
            (Profile.subtract_result_retire call preserved.cells next
              (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1)
              (result.as_subtract keptRight small)))
      conv in scalarFirstDecision => cbv
      conv at finish in scalarSmallCall => cbv
      cil_contract_steps [found, binaryArguments, fl, fo, slot,
        load_local_word64_of_read loaded] until finish)
  exact ⟨fuel, final, values, invoke_of_run found
    (checkedValues_of_valid call.binary_arguments_valid) setup finished, result⟩

end UInt256Proof.Subtract.Safety
