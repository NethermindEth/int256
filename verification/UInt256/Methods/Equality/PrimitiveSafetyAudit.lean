import UInt256.Methods.Equality.PrimitiveFamilySafety
import UInt256.Methods.Equality.PrimitiveSafetyContract
import UInt256.Safety.ReadOnlyScalarContract
import UInt256.Methods.Equality.PrimitiveSafetyPrefix64

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem checked_primitive_contract :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      Extracted.program Extracted.entryIndex := by
  intro memory left right call
  exact primitive_checked memory left (.i64 right) right rfl (primitive_prefix64 right) call

theorem checked_primitive_binding :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      Extracted.program Extracted.entryIndex := checked_primitive_contract

#print axioms checked_primitive_contract
#print axioms checked_primitive_binding

theorem checked_primitive_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex := checked_scalar_family checked_primitive_contract profile valid same

#print axioms checked_primitive_family

end UInt256Proof.Equality.Safety
