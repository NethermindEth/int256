import UInt256.Methods.Multiply.Correctness
import CIL.MultiplyFeatures
import CIL.MultiplyProfileCoverage
open CIL UInt256Model
namespace UInt256Proof.Multiply

theorem checked_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial left right out,
      Contract (reprofile Extracted.program profile) Extracted.entryIndex initial left right out := by
  intro profile _ agreement initial left right out
  obtain ⟨fuel, final, execution, bytes⟩ := multiply_correct initial left right out
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

theorem checked_family_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.profile.classifyMultiply = profile.classifyMultiply →
    Extracted.profile.vector256Accelerated = profile.vector256Accelerated →
    ∀ initial left right out,
      Contract (reprofile Extracted.program profile) Extracted.entryIndex initial left right out := by
  intro profile valid same storage
  apply checked_profile_contract profile valid
  have arithmetic := FeatureProfile.multiply_classification_agreement
    Extracted.profile profile Extracted.profileValid valid same
  exact multiply_profile_agreement Extracted.program Extracted.profile profile
    Extracted.profileValid valid (by decide)
    (congrArg (fun flags => flags.1) arithmetic)
    (congrArg (fun flags => flags.2.1) arithmetic)
    (congrArg (fun flags => flags.2.2.1) arithmetic)
    (congrArg (fun flags => flags.2.2.2) arithmetic) storage

end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.checked_contract
#print axioms UInt256Proof.Multiply.checked_profile_contract
#print axioms UInt256Proof.Multiply.checked_family_contract
