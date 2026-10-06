import UInt256.Methods.Multiply.InitializedSafety
import UInt256.Safety.ProfileContracts
import CIL.MultiplyFeatures
import CIL.MultiplyProfileCoverage

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_checked_contract (word : WordContract) (top : FullTopContract) :
    WrappingBinaryContract (fun left right => left * right) Extracted.program multiplyIndex :=
  (multiply_initialized_contract word top).to_wrapping

theorem multiply_family_contract
    (checked : WrappingBinaryContract (fun left right => left * right) Extracted.program multiplyIndex)
    (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.classifyMultiply = profile.classifyMultiply)
    (storage : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    WrappingBinaryContract (fun left right => left * right)
      (CIL.reprofile Extracted.program profile) multiplyIndex := by
  have arithmetic := CIL.FeatureProfile.multiply_classification_agreement
    Extracted.profile profile Extracted.profileValid valid same
  apply WrappingBinaryContract.reprofile
    (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.multiply_profile_agreement Extracted.program Extracted.profile profile
      Extracted.profileValid valid (by decide)
      (congrArg (fun flags => flags.1) arithmetic)
      (congrArg (fun flags => flags.2.1) arithmetic)
      (congrArg (fun flags => flags.2.2.1) arithmetic)
      (congrArg (fun flags => flags.2.2.2) arithmetic) storage)
  exact checked

#print axioms multiply_checked_contract
#print axioms multiply_family_contract
end UInt256Proof.Multiply.Safety
