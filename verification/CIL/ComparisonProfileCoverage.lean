import CIL.ProfileEquivalence

namespace CIL

/-- A full-width portable reduction skips the SSE4.1 query. Otherwise only
these two dispatch queries may observe a profile. -/
def referenceEqualityProfileCheck (vector : Bool) : Op → Bool
  | .feature .vector256Accelerated => true
  | .feature .sse41 => !vector
  | op => op.profileIndependentCheck

def referenceEqualityProgramCheck (program : Program) (vector : Bool) : Bool :=
  program.all fun body => body.code.all (referenceEqualityProfileCheck vector)

theorem reference_equality_profile_agreement (program : Program) (p q : FeatureProfile)
    (checked : referenceEqualityProgramCheck program p.vector256Accelerated = true)
    (vector : p.vector256Accelerated = q.vector256Accelerated)
    (sse : p.vector256Accelerated = false → p.sse41 = q.sse41) :
    program.ProfileAgreement p q := by
  intro body member op instruction
  have hb := List.all_eq_true.mp checked body member
  have ho := List.all_eq_true.mp hb op instruction
  cases op <;> simp [referenceEqualityProfileCheck, Op.profileIndependentCheck,
    Op.ProfileAgreement] at *
  case feature feature =>
    cases feature <;> simp_all [FeatureProfile.evaluate]
  case intrinsic operation _ =>
    cases operation <;> simp_all [Intrinsic.available]

end CIL

#print axioms CIL.reference_equality_profile_agreement
