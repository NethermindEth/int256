import UInt256.Methods.Bitwise.Xor

open CIL UInt256Model
namespace UInt256Proof.Bitwise

theorem checked_xor_contract : ∀ initial left right out,
    UInt256Model.Bitwise.Contract Extracted.program Extracted.entryIndex .xor
      initial left right out := xor_correct

/-- Transport only profiles agreeing on this actual program's operations. -/
theorem checked_xor_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial left right out,
      UInt256Model.Bitwise.Contract (reprofile Extracted.program profile)
        Extracted.entryIndex .xor initial left right out := by
  intro profile _ agreement initial left right out
  obtain ⟨fuel, final, execution, bytes⟩ := xor_correct initial left right out
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

#print axioms checked_xor_contract
#print axioms checked_xor_profile_contract
end UInt256Proof.Bitwise
