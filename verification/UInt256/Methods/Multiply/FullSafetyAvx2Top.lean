import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.VectorInputs
import UInt256.Methods.Multiply.VectorSteps

/-! The AVX2 top product carries initialized word and vector homes through shared snapshots. -/

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

/-- The checked AVX2 path computes the top product while preserving caller and private words. -/
theorem full_avx2_top (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true) :
    FullTopContract profile program methodIndex wordIndex countIndex storageIndex := by
  intro original entered current left right output frame originalCall enteredWF homes state
    post continuation
  have profileEq : (fullBody profile wordIndex countIndex storageIndex).profile = profile := rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have loadedLeft := input_vector_snapshot state originalCall left (by simp)
  have formed := state.call.1.1
  have retained := state.authority
  cil_contract_steps (snapshots := state.snapshots.toLocalSnapshots) [found, productArgs,
    formedLeft, loadedLeft, profileEq, noAvx512, avx2, CIL.FeatureProfile.evaluate]
  have middleState := state.after_vector_write homes (by assumption) localWrite
  have formedRight := middleState.call.input_formed (by simp : right ∈ [left, right])
  have loadedRight := input_vector_snapshot middleState originalCall right (by simp)
  cil_contract_steps (snapshots := localSnapshots) [found, productArgs, formedRight, loadedRight,
    profileEq, noAvx512, avx2, eval_reverse256, step_reinterpret256, step_shift_right256,
    step_even_product256, step_shift_left256, step_add256, step_sum256] until continuation _ (by
      have crossState := (middleState.after_vector_write homes (by assumption)
        localWrite_1).after_vector_write homes (by assumption) localWrite_2
      simpa only [digitLow_shift32, narrow_low_correct, lowProduct, fullTop] using
        crossState.after_word_write homes (by assumption) localWrite_3)

end UInt256Proof.Multiply.Full
