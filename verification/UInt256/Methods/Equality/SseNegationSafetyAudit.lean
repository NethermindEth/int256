import UInt256.Methods.Equality.ReferenceFamilySafety
import UInt256.Methods.Equality.NegationSafetyContract
import UInt256.Methods.Equality.SseSafetyContract

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem checked_inequality_contract :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 ≠ values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 :=
  inequality_readOnly_contract
    (wrapper_checked true (by rfl) (wrapper_checked false (by rfl) sse_checked))

theorem checked_inequality_binding :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 ≠ values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := checked_inequality_contract

#print axioms checked_inequality_contract
#print axioms checked_inequality_binding

theorem checked_inequality_family (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 ≠ values[1]?.getD 0 then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex 2 :=
  ReadOnlyContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (checked_reference_profile_agreement profile vector sse) checked_inequality_contract

#print axioms checked_inequality_family

end UInt256Proof.Equality.Safety
