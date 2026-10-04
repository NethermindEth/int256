import CIL.Features

namespace CIL

/-- Arithmetic dispatch distinctions for wrapping multiplication. Storage is
    independent and is covered separately by its acceleration flag. -/
inductive MultiplyClass where
  | softwareScalarTop | softwareAvx2Top | softwareDQVLTop
  | bmi2ScalarTop | bmi2Avx2Top | bmi2DQVLTop | arm64ScalarTop
  deriving DecidableEq, Repr

def MultiplyClass.all : List MultiplyClass :=
  [.softwareScalarTop, .softwareAvx2Top, .softwareDQVLTop,
   .bmi2ScalarTop, .bmi2Avx2Top, .bmi2DQVLTop, .arm64ScalarTop]

def FeatureProfile.classifyMultiply (p : FeatureProfile) : MultiplyClass :=
  if p.bmi2 then
    if p.avx512DQVL then .bmi2DQVLTop
    else if p.avx2 then .bmi2Avx2Top else .bmi2ScalarTop
  else if p.armBase64 then .arm64ScalarTop
  else if p.avx512DQVL then .softwareDQVLTop
  else if p.avx2 then .softwareAvx2Top else .softwareScalarTop

theorem FeatureProfile.multiply_classification_total (p : FeatureProfile) :
    p.classifyMultiply ∈ MultiplyClass.all := by
  cases p.classifyMultiply <;> simp [MultiplyClass.all]

private theorem arm_excludes_x64 (p : FeatureProfile) (valid : p.Valid)
    (arm : p.armBase64 = true) :
    p.bmi2 = false ∧ p.avx2 = false ∧ p.avx512DQVL = false := by
  rcases valid with ⟨_, _, _, x64, _, _, _, _, _, _, _, _, _, _, armArch, _⟩
  have disabled :
      (p.sse2 || p.ssse3 || p.sse42 || p.avx || p.avx2 || p.avx512F ||
       p.avx512FVL || p.bmi1 || p.sse41 || p.avx512DQ || p.avx512DQVL || p.bmi2) = false := by
    cases flags : (p.sse2 || p.ssse3 || p.sse42 || p.avx || p.avx2 || p.avx512F ||
      p.avx512FVL || p.bmi1 || p.sse41 || p.avx512DQ || p.avx512DQVL || p.bmi2)
    · rfl
    · have := x64 flags
      have := armArch arm
      simp_all
  simp_all [Bool.or_eq_false_iff]

def MultiplyClass.flags : MultiplyClass → Bool × Bool × Bool × Bool
  | .softwareScalarTop => (false, false, false, false)
  | .softwareAvx2Top => (false, false, false, true)
  | .softwareDQVLTop => (false, false, true, true)
  | .bmi2ScalarTop => (true, false, false, false)
  | .bmi2Avx2Top => (true, false, false, true)
  | .bmi2DQVLTop => (true, false, true, true)
  | .arm64ScalarTop => (false, true, false, false)

/-- In the declared capability domain, the class recovers every arithmetic
    feature query, including the AVX2 prerequisite of DQ.VL. -/
theorem FeatureProfile.multiply_classification_flags (p : FeatureProfile) (valid : p.Valid) :
    p.classifyMultiply.flags = (p.bmi2, p.armBase64, p.avx512DQVL, p.avx2) := by
  have arm := arm_excludes_x64 p valid
  have dq : p.avx512DQVL = true → p.avx2 = true := by
    intro enabled
    rcases valid with ⟨_, _, _, _, _, _, _, _, _, fAvx, _, _, dqF, dqVL, _, _⟩
    exact fAvx (dqF (dqVL enabled).1)
  cases hb : p.bmi2 <;> cases ha : p.armBase64 <;>
    cases hd : p.avx512DQVL <;> cases hv : p.avx2 <;>
    simp_all [FeatureProfile.classifyMultiply, MultiplyClass.flags]

theorem FeatureProfile.multiply_classification_agreement (p q : FeatureProfile)
    (hp : p.Valid) (hq : q.Valid) (same : p.classifyMultiply = q.classifyMultiply) :
    (p.bmi2, p.armBase64, p.avx512DQVL, p.avx2) =
      (q.bmi2, q.armBase64, q.avx512DQVL, q.avx2) := by
  rw [← p.multiply_classification_flags hp, ← q.multiply_classification_flags hq, same]

end CIL
#print axioms CIL.FeatureProfile.multiply_classification_flags
