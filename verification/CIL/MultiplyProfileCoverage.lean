import CIL.ProfileEquivalence
namespace CIL

/-- Check actual operations, including the availability of retained ISA calls. -/
def multiplyProfileCheck (profile : FeatureProfile) : Op → Bool
  | .feature .bmi2 | .feature .armBase64 | .feature .avx512DQVL
  | .feature .avx2 | .feature .vector256Accelerated => true
  | .intrinsic (.bmi2 _) _ => profile.bmi2
  | .intrinsic (.armBase64 _) _ => profile.armBase64
  | .intrinsic (.avx2 _) _ => profile.avx2
  | .intrinsic (.avx512DQ .mul64) _ => profile.avx512DQVL
  | op => op.profileIndependentCheck

def multiplyProgramCheck (program : Program) (profile : FeatureProfile) : Bool :=
  program.all fun body => body.code.all (multiplyProfileCheck profile)

private theorem dqvl_capabilities (p : FeatureProfile) (valid : p.Valid)
    (enabled : p.avx512DQVL = true) :
    p.avx512DQ = true ∧ p.avx512F = true ∧ p.avx512FVL = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, dq, dqvl, _, _⟩ := valid
  have caps := dqvl enabled
  exact ⟨caps.1, dq caps.1, caps.2⟩

theorem multiply_profile_agreement (program : Program) (p q : FeatureProfile)
    (hp : p.Valid) (hq : q.Valid)
    (checked : multiplyProgramCheck program p = true)
    (bmi : p.bmi2 = q.bmi2) (arm : p.armBase64 = q.armBase64)
    (dq : p.avx512DQVL = q.avx512DQVL) (avx : p.avx2 = q.avx2)
    (storage : p.vector256Accelerated = q.vector256Accelerated) : program.ProfileAgreement p q := by
  have pCaps := dqvl_capabilities p hp
  have qCaps := dqvl_capabilities q hq
  intro body member op instruction
  have hb := List.all_eq_true.mp checked body member
  have ho := List.all_eq_true.mp hb op instruction
  cases op <;> simp [multiplyProfileCheck, Op.profileIndependentCheck,
    Op.ProfileAgreement] at *
  case feature feature =>
    cases feature <;> simp_all [FeatureProfile.evaluate]
  case intrinsic operation _ =>
    cases operation <;> simp_all [Intrinsic.available]
    case avx512DQ operation =>
      cases operation <;> have retained := hb _ instruction
      all_goals simp_all [Intrinsic.available]

end CIL
#print axioms CIL.multiply_profile_agreement
