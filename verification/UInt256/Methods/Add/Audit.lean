import UInt256.Methods.Add.Examples
import UInt256.FeatureCoverage

-- This gate deliberately cannot compile until the full, unrestricted public
-- contract is proved. A weaker helper statement cannot satisfy this type.
namespace UInt256Proof
theorem checked_contract : ∀ (initial : UInt256Model.Bytes) (left right out : Nat),
    UInt256Model.Contract Extracted.program Extracted.entryIndex initial left right out := add_correct

theorem checked_contract_family : ∀ (profile : CIL.FeatureProfile), profile.Valid →
    profile.classify = Extracted.profile.classify →
    ∀ (initial : UInt256Model.Bytes) (left right out : Nat),
    UInt256Model.Contract (CIL.reprofile Extracted.program profile)
      Extracted.entryIndex initial left right out := by
  intro profile valid family initial left right out
  exact (add_contract_profiles Extracted.program profile Extracted.profile valid
    Extracted.profileValid family
    (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    Extracted.programClassified _ initial left right out).mp
      (checked_contract initial left right out)

-- This is the exact certificate consumed by the aggregate composition rule.
theorem checked_add_family_certificate : AddFamily
    { program := Extracted.program, entry := Extracted.entryIndex }
    Extracted.profile.classify := checked_contract_family

theorem checked_profile_representative :
    Extracted.profile = Extracted.profile.classify.representative := by decide
end UInt256Proof

-- The final theorem's audit includes its transitive proof dependencies.
#print axioms UInt256Proof.checked_contract
#print axioms UInt256Proof.checked_contract_family
#print axioms UInt256Proof.checked_add_family_certificate
#print axioms UInt256Proof.checked_profile_representative
