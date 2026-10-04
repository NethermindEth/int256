import UInt256.FeatureCoverage
import CIL.FeatureCoverage

open CIL
namespace UInt256Proof

/-- A family supplies the selected mathematical contract for every profile
    with its storage-dispatch flag. Actual instruction checks are dependencies
    of the separately audited operation gates. -/
def VectorStorageFamily (contract : Program → Nat → Prop) (artifact : Representative) : Prop :=
  ∀ profile : FeatureProfile, profile.Valid →
    artifact.profile.vector256Accelerated = profile.vector256Accelerated →
    contract (reprofile artifact.program profile) artifact.entry

theorem vector_storage_complete_coverage (contract : Program → Nat → Prop)
    (scalar vector : Representative)
    (scalarFlag : scalar.profile.vector256Accelerated = false)
    (vectorFlag : vector.profile.vector256Accelerated = true)
    (scalarChecked : VectorStorageFamily contract scalar)
    (vectorChecked : VectorStorageFamily contract vector)
    (profile : FeatureProfile) (valid : profile.Valid) :
    ∃ artifact ∈ [scalar, vector], contract (reprofile artifact.program profile) artifact.entry := by
  cases flag : profile.vector256Accelerated with
  | false => exact ⟨scalar, by simp, scalarChecked profile valid (scalarFlag.trans flag.symm)⟩
  | true => exact ⟨vector, by simp, vectorChecked profile valid (vectorFlag.trans flag.symm)⟩

def ClassifiedFamily (contract : Program → Nat → Prop)
    (artifact : FamilyProgram) (family : FeatureClass) : Prop :=
  ∀ profile : FeatureProfile, profile.Valid → profile.classify = family →
    contract (reprofile artifact.program profile) artifact.entry

/-- Portable vector reduction dispatches on acceleration first, and on SSE4.1
    only when the 256-bit path is disabled. Each gate must prove this condition
    sufficient for agreement of its actual extracted instructions. -/
def VectorReductionFamily (contract : Program → Nat → Prop) (artifact : Representative) : Prop :=
  ∀ profile : FeatureProfile, profile.Valid →
    artifact.profile.vector256Accelerated = profile.vector256Accelerated →
    (artifact.profile.vector256Accelerated = false → artifact.profile.sse41 = profile.sse41) →
    contract (reprofile artifact.program profile) artifact.entry

theorem vector_reduction_complete_coverage (contract : Program → Nat → Prop)
    (scalar sse vector : Representative)
    (scalarVector : scalar.profile.vector256Accelerated = false)
    (scalarSse : scalar.profile.sse41 = false)
    (sseVector : sse.profile.vector256Accelerated = false)
    (sseSse : sse.profile.sse41 = true)
    (vectorFlag : vector.profile.vector256Accelerated = true)
    (scalarChecked : VectorReductionFamily contract scalar)
    (sseChecked : VectorReductionFamily contract sse)
    (vectorChecked : VectorReductionFamily contract vector)
    (profile : FeatureProfile) (valid : profile.Valid) :
    ∃ artifact ∈ [scalar, sse, vector], contract (reprofile artifact.program profile) artifact.entry := by
  cases flag : profile.vector256Accelerated with
  | true =>
    refine ⟨vector, by simp, vectorChecked profile valid (vectorFlag.trans flag.symm) ?_⟩
    intro disabled
    simp [vectorFlag] at disabled
  | false =>
    cases sseFlag : profile.sse41 with
    | false =>
      exact ⟨scalar, by simp, scalarChecked profile valid
        (scalarVector.trans flag.symm) (fun _ => scalarSse.trans sseFlag.symm)⟩
    | true =>
      exact ⟨sse, by simp, sseChecked profile valid
        (sseVector.trans flag.symm) (fun _ => sseSse.trans sseFlag.symm)⟩

theorem classified_complete_coverage (contract : Program → Nat → Prop)
    (artifacts : FeatureClass → FamilyProgram)
    (checked : ∀ family ∈ FeatureClass.all, ClassifiedFamily contract (artifacts family) family)
    (profile : FeatureProfile) (valid : profile.Valid) :
    contract (reprofile (artifacts profile.classify).program profile)
      (artifacts profile.classify).entry :=
  checked profile.classify profile.classification_total profile valid rfl

/-- Relational dispatch observes AVX512F.VL first, then AVX2, then portable
    vector acceleration. Lower-priority flags do not constrain earlier paths. -/
def RelationalFamily (contract : Program → Nat → Prop) (artifact : Representative) : Prop :=
  ∀ profile : FeatureProfile, profile.Valid →
    artifact.profile.avx512FVL = profile.avx512FVL →
    (artifact.profile.avx512FVL = false → artifact.profile.avx2 = profile.avx2) →
    (artifact.profile.avx512FVL = false → artifact.profile.avx2 = false →
      artifact.profile.vector256Accelerated = profile.vector256Accelerated) →
    contract (reprofile artifact.program profile) artifact.entry

theorem relational_complete_coverage (contract : Program → Nat → Prop)
    (scalar vector avx native : Representative)
    (scalarNative : scalar.profile.avx512FVL = false)
    (scalarAvx : scalar.profile.avx2 = false)
    (scalarVector : scalar.profile.vector256Accelerated = false)
    (vectorNative : vector.profile.avx512FVL = false)
    (vectorAvx : vector.profile.avx2 = false)
    (vectorFlag : vector.profile.vector256Accelerated = true)
    (avxNative : avx.profile.avx512FVL = false)
    (avxFlag : avx.profile.avx2 = true)
    (nativeFlag : native.profile.avx512FVL = true)
    (scalarChecked : RelationalFamily contract scalar)
    (vectorChecked : RelationalFamily contract vector)
    (avxChecked : RelationalFamily contract avx)
    (nativeChecked : RelationalFamily contract native)
    (profile : FeatureProfile) (valid : profile.Valid) :
    ∃ artifact ∈ [scalar, vector, avx, native],
      contract (reprofile artifact.program profile) artifact.entry := by
  cases nativeValue : profile.avx512FVL with
  | true =>
    refine ⟨native, by simp, nativeChecked profile valid
      (nativeFlag.trans nativeValue.symm) ?_ ?_⟩
    all_goals intro disabled; simp [nativeFlag] at disabled
  | false =>
    cases avxValue : profile.avx2 with
    | true =>
      refine ⟨avx, by simp, avxChecked profile valid
        (avxNative.trans nativeValue.symm) (fun _ => avxFlag.trans avxValue.symm) ?_⟩
      intro _ disabled
      simp [avxFlag] at disabled
    | false =>
      cases vectorValue : profile.vector256Accelerated with
      | false =>
        exact ⟨scalar, by simp, scalarChecked profile valid
          (scalarNative.trans nativeValue.symm) (fun _ => scalarAvx.trans avxValue.symm)
          (fun _ _ => scalarVector.trans vectorValue.symm)⟩
      | true =>
        exact ⟨vector, by simp, vectorChecked profile valid
          (vectorNative.trans nativeValue.symm) (fun _ => vectorAvx.trans avxValue.symm)
          (fun _ _ => vectorFlag.trans vectorValue.symm)⟩

end UInt256Proof
#print axioms UInt256Proof.vector_storage_complete_coverage
#print axioms UInt256Proof.classified_complete_coverage
#print axioms UInt256Proof.vector_reduction_complete_coverage
#print axioms UInt256Proof.relational_complete_coverage
