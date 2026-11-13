import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.VectorInputs
import UInt256.Methods.Multiply.VectorSteps

/-! The checked AVX512 top product preserves the caller and initialized word homes. -/

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

/-- The enabled AVX512 path multiplies reversed lanes and stores their exact sum. -/
theorem full_avx512_top (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (enabled : profile.avx512DQVL = true) (avx2 : profile.avx2 = true)
    (dq : profile.avx512DQ = true) (foundation : profile.avx512F = true) (vl : profile.avx512FVL = true) :
    FullTopContract profile program methodIndex wordIndex countIndex storageIndex := by
  intro original entered current left right output frame originalCall enteredWF homes state
    post continuation
  have profileEq : (fullBody profile wordIndex countIndex storageIndex).profile = profile := rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have formedRight := state.call.input_formed (by simp : right ∈ [left, right])
  have loadedLeft := input_vector_snapshot state originalCall left (by simp)
  have loadedRight := input_vector_snapshot state originalCall right (by simp)
  have formed := state.call.1.1
  have retained := state.authority
  cil_contract_steps (snapshots := state.snapshots.toLocalSnapshots) [found, productArgs,
    formedLeft, formedRight, loadedLeft, loadedRight, profileEq, enabled, avx2, dq, foundation,
    vl, CIL.FeatureProfile.evaluate, CIL.Intrinsic.available, step_reverse256, step_mul256,
    step_sum256] until continuation _ (by
      simpa only [fullTop] using (state.after_vector_write homes (by assumption)
        localWrite).after_word_write homes (by assumption) localWrite_1)

end UInt256Proof.Multiply.Full