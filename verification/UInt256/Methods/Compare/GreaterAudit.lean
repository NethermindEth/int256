import UInt256.Methods.Compare.Greater

open CIL UInt256Model
namespace UInt256Proof.Compare

theorem checked_greater_contract : ∀ initial left right,
    UInt256Model.Compare.Contract Extracted.program Extracted.entryIndex .greater
      initial left right := greater_correct

/-- Transport only profiles agreeing on this actual program's operations. -/
theorem checked_greater_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial left right,
      UInt256Model.Compare.Contract (reprofile Extracted.program profile)
        Extracted.entryIndex .greater initial left right := by
  intro profile _ agreement initial left right
  obtain ⟨fuel, final, execution, bytes⟩ := greater_correct initial left right
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

#print axioms checked_greater_contract
#print axioms checked_greater_profile_contract
end UInt256Proof.Compare
