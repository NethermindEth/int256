import UInt256.Methods.Subtract.Correctness
import Tests.SubtractSemantics
import UInt256.FeatureCoverage

namespace UInt256Proof
-- This exact gate cannot be satisfied by a helper or a narrowed aliasing theorem.
theorem checked_subtract_contract : ∀ (initial : UInt256Model.Bytes) (left right out : Nat),
    UInt256Model.SubtractContract Extracted.program Extracted.entryIndex initial left right out := subtract_correct

theorem checked_subtract_contract_family : ∀ (profile : CIL.FeatureProfile), profile.Valid →
    profile.classify = Extracted.profile.classify →
    ∀ (initial : UInt256Model.Bytes) (left right out : Nat),
    UInt256Model.SubtractContract (CIL.reprofile Extracted.program profile)
      Extracted.entryIndex initial left right out := by
  intro profile valid family initial left right out
  exact (subtract_contract_profiles Extracted.program profile Extracted.profile valid
    Extracted.profileValid family
    (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    Extracted.programClassified _ initial left right out).mp
      (checked_subtract_contract initial left right out)

theorem checked_subtract_family_certificate : SubtractFamily
    { program := Extracted.program, entry := Extracted.entryIndex }
    Extracted.profile.classify := checked_subtract_contract_family

theorem checked_profile_representative :
    Extracted.profile = Extracted.profile.classify.representative := by decide
end UInt256Proof

#print axioms UInt256Proof.checked_subtract_contract
#print axioms UInt256Proof.checked_subtract_contract_family
#print axioms UInt256Proof.checked_subtract_family_certificate
#print axioms UInt256Proof.checked_profile_representative
