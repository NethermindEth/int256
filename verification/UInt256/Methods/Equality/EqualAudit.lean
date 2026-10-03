import UInt256.Methods.Equality.Equal

open CIL UInt256Model
namespace UInt256Proof.Equality

theorem checked_equal_contract : ∀ initial left right,
    UInt256Model.Equality.Contract Extracted.program Extracted.entryIndex
      initial left right := equal_correct

/-- Transport only profiles agreeing on this actual program's operations. -/
theorem checked_equal_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial left right,
      UInt256Model.Equality.Contract (reprofile Extracted.program profile)
        Extracted.entryIndex initial left right := by
  intro profile _ agreement initial left right
  obtain ⟨fuel, final, execution, bytes⟩ := equal_correct initial left right
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

#print axioms checked_equal_contract
#print axioms checked_equal_profile_contract
end UInt256Proof.Equality
