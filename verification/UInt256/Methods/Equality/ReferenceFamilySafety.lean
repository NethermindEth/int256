import UInt256.Safety.ProfileContracts
import CIL.ComparisonProfileCoverage
import Extracted

namespace UInt256Proof.Equality.Safety

theorem checked_reference_profile_agreement (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    Extracted.program.ProfileAgreement Extracted.profile profile :=
  CIL.reference_equality_profile_agreement Extracted.program _ _ (by decide) vector sse

end UInt256Proof.Equality.Safety
