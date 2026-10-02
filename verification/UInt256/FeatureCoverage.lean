import UInt256.ProfileContracts

open CIL UInt256Model

namespace UInt256Proof

/-- Expanding the classifier requires expanding the aggregate certificate gate.
    In particular, a new constructor cannot silently inherit seven reports. -/
theorem checked_feature_classes : FeatureClass.all =
    [.scalar, .arm64, .sse, .avx2 false, .avx2 true, .avx512 false, .avx512 true] := rfl

theorem checked_representative_classes (family : FeatureClass) :
    family.representative.classify = family := by
  cases family with
  | scalar => rfl
  | arm64 => rfl
  | sse => rfl
  | avx2 bmi => cases bmi <;> rfl
  | avx512 bmi => cases bmi <;> rfl

/-- Each entry is the actual extracted program and public entry for one family.
    The programs may differ because extraction retains only reachable code. -/
structure FamilyProgram where
  program : Program
  entry : Nat

def AddFamily (artifact : FamilyProgram) (family : FeatureClass) : Prop :=
  ∀ profile : FeatureProfile, profile.Valid → profile.classify = family →
    ∀ (initial : Bytes) (left right out : Nat),
      Contract (reprofile artifact.program profile) artifact.entry initial left right out

def SubtractFamily (artifact : FamilyProgram) (family : FeatureClass) : Prop :=
  ∀ profile : FeatureProfile, profile.Valid → profile.classify = family →
    ∀ (initial : Bytes) (left right out : Nat),
      SubtractContract (reprofile artifact.program profile) artifact.entry initial left right out

/-- Checked composition rule: all seven full family certificates cover every
    valid profile, including runtime-disabled features. This theorem does not
    supply the certificates; the aggregate runner requires fresh audited gates
    for every actual method/family artifact before issuing a success report. -/
theorem add_complete_coverage (artifacts : FeatureClass → FamilyProgram)
    (certificates : ∀ family ∈ FeatureClass.all, AddFamily (artifacts family) family)
    (profile : FeatureProfile) (valid : profile.Valid)
    (initial : Bytes) (left right out : Nat) :
    Contract (reprofile (artifacts profile.classify).program profile)
      (artifacts profile.classify).entry initial left right out :=
  certificates profile.classify profile.classification_total profile valid rfl
    initial left right out

theorem subtract_complete_coverage (artifacts : FeatureClass → FamilyProgram)
    (certificates : ∀ family ∈ FeatureClass.all, SubtractFamily (artifacts family) family)
    (profile : FeatureProfile) (valid : profile.Valid)
    (initial : Bytes) (left right out : Nat) :
    SubtractContract (reprofile (artifacts profile.classify).program profile)
      (artifacts profile.classify).entry initial left right out :=
  certificates profile.classify profile.classification_total profile valid rfl
    initial left right out

end UInt256Proof

#print axioms CIL.FeatureProfile.classification_total
#print axioms UInt256Proof.checked_feature_classes
#print axioms UInt256Proof.checked_representative_classes
#print axioms UInt256Proof.add_complete_coverage
#print axioms UInt256Proof.subtract_complete_coverage
