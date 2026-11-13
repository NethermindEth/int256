import UInt256.Safety.ProfileContracts
import CIL.ProfileEquivalence
import UInt256.Methods.Bindings

namespace UInt256Proof.Equality.Safety

theorem checked_reference_profile_agreement (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    Extracted.program.ProfileAgreement Extracted.profile profile :=
  by
    intro body member op instruction
    simp only [Extracted.program, List.mem_cons, List.not_mem_nil, or_false] at member
    repeat' first
      | subst body
      | rcases member with rfl | member
    all_goals
      conv at instruction => lhs; cbv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at instruction
      repeat' first
        | solve | simp_all [CIL.Op.ProfileAgreement, CIL.FeatureProfile.evaluate, Extracted.profile]
        | rcases instruction with rfl | instruction


end UInt256Proof.Equality.Safety
