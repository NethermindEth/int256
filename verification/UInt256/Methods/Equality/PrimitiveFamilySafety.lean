import UInt256.Safety.ProfileContracts
import CIL.StorageProfileCoverage
import Extracted

namespace UInt256Proof.Equality.Safety
open UInt256Model.Safety

/-- The actual extracted program must observe only portable storage dispatch. -/
theorem checked_scalar_family {α : Type} {encode : α → CIL.Value}
    {operation : BitVec 256 → α → CIL.Value} {method : Nat}
    (checked : ReadOnlyScalarContract encode operation Extracted.program method)
    (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract encode operation (CIL.reprofile Extracted.program profile) method :=
  ReadOnlyScalarContract.reprofile
    (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.storage_profile_agreement Extracted.program (by decide) _ _ same) checked

end UInt256Proof.Equality.Safety
