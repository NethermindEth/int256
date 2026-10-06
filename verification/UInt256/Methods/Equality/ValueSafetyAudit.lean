import UInt256.Methods.Equality.ReferenceFamilySafety
import UInt256.Methods.Equality.ValueSafetyContract
import UInt256.Methods.Equality.ScalarSafetyContract

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem checked_value_contract :
    ReadOnlyValueContract (fun left right => .i32 (if left = right then 1 else 0))
      Extracted.program Extracted.entryIndex :=
  value_entry_checked (wrapper_checked false (by rfl) scalar_checked)

theorem checked_value_binding :
    ReadOnlyValueContract (fun left right => .i32 (if left = right then 1 else 0))
      Extracted.program Extracted.entryIndex := checked_value_contract

#print axioms checked_value_contract
#print axioms checked_value_binding

theorem checked_value_family (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    ReadOnlyValueContract (fun left right => .i32 (if left = right then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex :=
  ReadOnlyValueContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (checked_reference_profile_agreement profile vector sse) checked_value_contract

#print axioms checked_value_family

end UInt256Proof.Equality.Safety
