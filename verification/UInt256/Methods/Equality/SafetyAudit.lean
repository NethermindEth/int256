import UInt256.Methods.Equality.ReferenceFamilySafety
import UInt256.Methods.Equality.WrapperSafetyContract
import UInt256.Methods.Equality.ScalarSafetyContract

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem equality_entry_checked : EqualityInvocation Extracted.entryIndex := by
  first
  | exact wrapper_checked false (by rfl) scalar_checked
  | exact wrapper_checked true (by rfl) (wrapper_checked false (by rfl) scalar_checked)

theorem checked_equality_contract :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 :=
  equality_readOnly_contract equality_entry_checked

theorem checked_equality_binding :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := checked_equality_contract

#print axioms checked_equality_contract
#print axioms checked_equality_binding

theorem checked_equality_family (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex 2 :=
  ReadOnlyContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (checked_reference_profile_agreement profile vector sse) checked_equality_contract

#print axioms checked_equality_family

end UInt256Proof.Equality.Safety
