import UInt256.Methods.Bitwise.Xor
import CIL.StorageProfileCoverage

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

theorem checked_xor_family_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.profile.vector256Accelerated = profile.vector256Accelerated →
    ∀ initial left right out,
      UInt256Model.Bitwise.Contract (reprofile Extracted.program profile)
        Extracted.entryIndex .xor initial left right out := by
  intro profile valid vector
  apply checked_xor_profile_contract profile valid
  exact storage_profile_agreement Extracted.program (by decide) _ _ vector

#print axioms checked_xor_contract
#print axioms checked_xor_profile_contract
#print axioms checked_xor_family_contract
end UInt256Proof.Bitwise
