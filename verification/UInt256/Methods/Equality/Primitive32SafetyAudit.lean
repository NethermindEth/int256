import UInt256.Methods.Equality.PrimitiveFamilySafety
import UInt256.Methods.Equality.PrimitiveSafetyContract
import UInt256.Methods.Equality.PrimitiveSafetyPrefix32
import UInt256.Safety.ReadOnlyScalarContract

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem checked_primitive_contract :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      Extracted.program Extracted.entryIndex := by
  intro memory left right call
  have checked := primitive_checked memory left (.i32 right) (right.zeroExtend 64) rfl
    (primitive_prefix32 right) call
  have widened : (right.zeroExtend 64).toNat = right.toNat := by
    have bound := right.isLt
    simp
    omega
  rw [widened] at checked
  exact checked

theorem checked_primitive_binding :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      Extracted.program Extracted.entryIndex := checked_primitive_contract

#print axioms checked_primitive_contract
#print axioms checked_primitive_binding

theorem checked_primitive_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex := checked_scalar_family checked_primitive_contract profile valid same

#print axioms checked_primitive_family

end UInt256Proof.Equality.Safety
