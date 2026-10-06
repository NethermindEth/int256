import Extracted
import UInt256.Safety.ProfileContracts
import CIL.MultiplyFeatures
import CIL.MultiplyProfileCoverage

namespace UInt256Proof.Multiply.Safety

theorem selected_profile_agreement (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.classifyMultiply = profile.classifyMultiply)
    (storage : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    Extracted.program.ProfileAgreement Extracted.profile profile := by
  have arithmetic := CIL.FeatureProfile.multiply_classification_agreement
    Extracted.profile profile Extracted.profileValid valid same
  exact CIL.multiply_profile_agreement Extracted.program Extracted.profile profile
    Extracted.profileValid valid (by decide)
    (congrArg (fun flags => flags.1) arithmetic)
    (congrArg (fun flags => flags.2.1) arithmetic)
    (congrArg (fun flags => flags.2.2.1) arithmetic)
    (congrArg (fun flags => flags.2.2.2) arithmetic) storage

#print axioms selected_profile_agreement
end UInt256Proof.Multiply.Safety
