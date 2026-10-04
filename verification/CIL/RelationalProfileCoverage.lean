import CIL.ProfileEquivalence
namespace CIL

def relationalProfileCheck (native avx2 : Bool) : Op → Bool
  | .feature .avx512FVL => true
  | .feature .avx2 => !native
  | .feature .vector256Accelerated => !native && !avx2
  | .intrinsic (.avx _) _ | .intrinsic (.avx2 _) _ | .intrinsic (.avx512 _) _ => native
  | op => op.profileIndependentCheck

def relationalProgramCheck (program : Program) (native avx2 : Bool) : Bool :=
  program.all fun body => body.code.all (relationalProfileCheck native avx2)

private theorem native_capabilities (p : FeatureProfile) (valid : p.Valid)
    (native : p.avx512FVL = true) : p.avx512F = true ∧ p.avx2 = true ∧ p.avx = true := by
  simp only [FeatureProfile.Valid] at valid
  obtain ⟨_, _, _, _, _, _, hAvx2, hVL, _, hF, _⟩ := valid
  have hf := hVL native
  have ha2 := hF hf
  exact ⟨hf, ha2, hAvx2 ha2⟩

theorem relational_profile_agreement (program : Program) (p q : FeatureProfile)
    (hp : p.Valid) (hq : q.Valid)
    (checked : relationalProgramCheck program p.avx512FVL p.avx2 = true)
    (native : p.avx512FVL = q.avx512FVL)
    (avx2 : p.avx512FVL = false → p.avx2 = q.avx2)
    (vector : p.avx512FVL = false → p.avx2 = false →
      p.vector256Accelerated = q.vector256Accelerated) : program.ProfileAgreement p q := by
  have pCaps := native_capabilities p hp
  have qCaps := native_capabilities q hq
  intro body member op instruction
  have hb := List.all_eq_true.mp checked body member
  have ho := List.all_eq_true.mp hb op instruction
  cases op <;> simp [relationalProfileCheck, Op.profileIndependentCheck,
    Op.ProfileAgreement] at *
  case feature feature =>
    cases feature <;> simp_all [FeatureProfile.evaluate]
  case intrinsic operation _ =>
    cases hnative : p.avx512FVL <;> cases operation <;>
      simp_all [Intrinsic.available]
end CIL
#print axioms CIL.relational_profile_agreement
