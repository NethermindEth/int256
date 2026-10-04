import UInt256.Methods.Equality.Unequal
import CIL.ComparisonProfileCoverage

open CIL UInt256Model
namespace UInt256Proof.Equality

theorem checked_unequal_contract : ∀ initial left right,
    UInt256Model.Equality.InequalityContract Extracted.program Extracted.entryIndex
      initial left right := unequal_correct

/-- Transport only profiles agreeing on this actual program's operations. -/
theorem checked_unequal_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial left right,
      UInt256Model.Equality.InequalityContract (reprofile Extracted.program profile)
        Extracted.entryIndex initial left right := by
  intro profile _ agreement initial left right
  obtain ⟨fuel, final, execution, bytes⟩ := unequal_correct initial left right
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

theorem checked_unequal_family_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.profile.vector256Accelerated = profile.vector256Accelerated →
    (Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) →
    ∀ initial left right,
      UInt256Model.Equality.InequalityContract (reprofile Extracted.program profile)
        Extracted.entryIndex initial left right := by
  intro profile valid vector sse
  apply checked_unequal_profile_contract profile valid
  exact reference_equality_profile_agreement Extracted.program Extracted.profile profile
    (by decide) vector sse

#print axioms checked_unequal_contract
#print axioms checked_unequal_profile_contract
#print axioms checked_unequal_family_contract
end UInt256Proof.Equality
