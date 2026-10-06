import UInt256.Methods.Equality.PrimitiveFamilySafety
import UInt256.Methods.Equality.VectorSigned32Safety

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem checked_signed_contract :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if right.toInt < 0 then 0 else
        if left = right.zeroExtend 256 then 1 else 0))
      Extracted.program Extracted.entryIndex := vector_signed_checked32

theorem checked_signed_binding :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if right.toInt < 0 then 0 else
        if left = right.zeroExtend 256 then 1 else 0))
      Extracted.program Extracted.entryIndex := checked_signed_contract

#print axioms checked_signed_contract
#print axioms checked_signed_binding

theorem checked_signed_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if right.toInt < 0 then 0 else
        if left = right.zeroExtend 256 then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex := checked_scalar_family checked_signed_contract profile valid same

#print axioms checked_signed_family

end UInt256Proof.Equality.Safety
