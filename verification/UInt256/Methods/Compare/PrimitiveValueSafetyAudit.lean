import UInt256.Methods.Compare.PrimitiveValueSafety

namespace UInt256Proof.Compare.PrimitiveValueSafety
open UInt256Model.Safety

theorem checked_binding : ScalarValueContract CIL.Value.i64
    (fun word input => .i32 (if word.toNat ≤ input.toNat then 1 else 0))
    Extracted.program Extracted.entryIndex := checked_contract

theorem checked_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid) :
    ScalarValueContract CIL.Value.i64
      (fun word input => .i32 (if word.toNat ≤ input.toNat then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex :=
  ScalarValueContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (Extracted.program.profile_independent_agreement (by decide) _ _) checked_contract

#print axioms checked_binding
#print axioms checked_family_contract
end UInt256Proof.Compare.PrimitiveValueSafety
