import Extracted
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.Compare.ProfileBindings
 theorem uniform : ∀ body ∈ Extracted.program, body.profile = Extracted.profile :=
  CIL.uniform_of_profile_map _ _ rfl
 theorem agreement (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (native : Extracted.profile.avx512FVL = profile.avx512FVL)
    (avx2 : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2)
    (vector : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false →
      Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    Extracted.program.ProfileAgreement Extracted.profile profile := by
  rcases valid with ⟨_, _, _, _, _, _, avx2Avx, fvlF, _, fAvx2, _⟩
  have nativeAvx2 (h : profile.avx512FVL = true) : profile.avx2 = true := fAvx2 (fvlF h)
  have nativeAvx (h : profile.avx512FVL = true) : profile.avx = true := avx2Avx (nativeAvx2 h)
  intro body member
  simp only [Extracted.program, List.mem_cons, List.not_mem_nil, or_false] at member
  repeat' first | subst body | rcases member with rfl | member
  all_goals
    conv => enter [op, 1]; lhs; cbv
    simp only [List.forall_mem_cons, List.forall_mem_nil, CIL.Op.ProfileAgreement,
      CIL.FeatureProfile.evaluate, CIL.Intrinsic.available, true_and, and_true]
    simp_all [Extracted.profile]
end UInt256Proof.Compare.ProfileBindings
