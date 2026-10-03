import UInt256.Methods.Bitwise.Not

open CIL UInt256Model
namespace UInt256Proof.Bitwise

theorem checked_not_contract : ∀ initial input out,
    UInt256Model.Bitwise.NotContract Extracted.program Extracted.entryIndex
      initial input out := not_correct

/-- Transport only profiles agreeing on this actual program's operations. -/
theorem checked_not_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial input out,
      UInt256Model.Bitwise.NotContract (reprofile Extracted.program profile)
        Extracted.entryIndex initial input out := by
  intro profile _ agreement initial input out
  obtain ⟨fuel, final, execution, bytes⟩ := not_correct initial input out
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

#print axioms checked_not_contract
#print axioms checked_not_profile_contract
end UInt256Proof.Bitwise
