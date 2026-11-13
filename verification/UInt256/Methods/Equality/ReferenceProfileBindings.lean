import Extracted
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.Equality.ProfileBindings
 theorem uniform : ∀ body ∈ Extracted.program, body.profile = Extracted.profile :=
  CIL.uniform_of_profile_map _ _ rfl
 theorem reference_agreement (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    Extracted.program.ProfileAgreement Extracted.profile profile := by
  intro body member op instruction
  simp only [Extracted.program, List.mem_cons, List.not_mem_nil, or_false] at member
  repeat' first | subst body | rcases member with rfl | member
  all_goals
    conv at instruction => lhs; cbv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at instruction
    repeat' first
      | solve | simp_all [CIL.Op.ProfileAgreement, CIL.FeatureProfile.evaluate, Extracted.profile, CIL.Intrinsic.available]
      | rcases instruction with rfl | instruction
end UInt256Proof.Equality.ProfileBindings
