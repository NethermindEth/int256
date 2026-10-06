import UInt256.Methods.Compare.LessEqualSafetyAudit
import UInt256.Safety.ProfileContracts
import CIL.RelationalProfileCoverage

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

theorem checked_less_equal_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (native : Extracted.profile.avx512FVL = profile.avx512FVL)
    (avx2 : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2)
    (vector : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false →
      Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat ≤ (values[1]?.getD 0).toNat then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex 2 :=
  ReadOnlyContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.relational_profile_agreement Extracted.program Extracted.profile profile
      Extracted.profileValid valid (by decide) native avx2 vector) checked_less_equal_contract

#print axioms checked_less_equal_family
end UInt256Proof.Compare.Safety
