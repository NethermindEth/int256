import UInt256.Methods.Compare.Less

open CIL UInt256Model
namespace UInt256Proof.Compare

theorem checked_less_contract : ∀ initial left right,
    UInt256Model.Compare.Contract Extracted.program Extracted.entryIndex .less
      initial left right := less_correct

/-- Transport only profiles agreeing on this actual program's operations. -/
theorem checked_less_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial left right,
      UInt256Model.Compare.Contract (reprofile Extracted.program profile)
        Extracted.entryIndex .less initial left right := by
  intro profile _ agreement initial left right
  obtain ⟨fuel, final, execution, bytes⟩ := less_correct initial left right
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

#print axioms checked_less_contract
#print axioms checked_less_profile_contract
end UInt256Proof.Compare
