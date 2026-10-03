import CIL.FeatureCoverage
open CIL
namespace UInt256Proof.Shift
/-- Traverses actual instructions; only portable storage dispatch may observe a profile. -/
def storageProfileCheck : Op → Bool
  | .feature .vector256Accelerated => true
  | op => op.profileIndependentCheck

def storageProgramCheck (program : Program) : Bool :=
  program.all fun body => body.code.all storageProfileCheck

theorem storage_profile_agreement (program : Program)
    (checked : storageProgramCheck program = true) (p q : FeatureProfile)
    (same : p.vector256Accelerated = q.vector256Accelerated) :
    program.ProfileAgreement p q := by
  intro body member op instruction
  have hb := List.all_eq_true.mp checked body member
  have ho := List.all_eq_true.mp hb op instruction
  cases op <;> simp [storageProfileCheck, Op.profileIndependentCheck,
    Op.ProfileAgreement] at *
  case feature feature =>
    cases feature <;> simp_all [FeatureProfile.evaluate]
  case intrinsic operation _ =>
    cases operation <;> simp_all [Intrinsic.available]

theorem storage_group_covered (scalar vector : Representative)
    (scalarUniform : ∀ body ∈ scalar.program, body.profile = scalar.profile)
    (vectorUniform : ∀ body ∈ vector.program, body.profile = vector.profile)
    (scalarCheck : storageProgramCheck scalar.program = true)
    (vectorCheck : storageProgramCheck vector.program = true)
    (scalarFlag : scalar.profile.vector256Accelerated = false)
    (vectorFlag : vector.profile.vector256Accelerated = true) :
    Representative.GroupCovered [scalar, vector] := by
  intro profile _
  cases flag : profile.vector256Accelerated with
  | false =>
    refine ⟨scalar, by simp, scalarUniform, ?_⟩
    exact storage_profile_agreement scalar.program scalarCheck _ _ (scalarFlag.trans flag.symm)
  | true =>
    refine ⟨vector, by simp, vectorUniform, ?_⟩
    exact storage_profile_agreement vector.program vectorCheck _ _ (vectorFlag.trans flag.symm)
end UInt256Proof.Shift
#print axioms UInt256Proof.Shift.storage_group_covered
