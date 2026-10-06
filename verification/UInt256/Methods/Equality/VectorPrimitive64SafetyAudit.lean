import UInt256.Methods.Equality.PrimitiveFamilySafety
import UInt256.Methods.Equality.VectorPrimitive64Safety
import UInt256.Methods.Equality.VectorPrimitiveWrapperContract

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem checked_primitive_contract :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
      Extracted.program Extracted.entryIndex :=
  vector_primitive_wrapper_checked CIL.Value.i64
    (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
    (fun _ => rfl) (fun _ _ => rfl) vector_primitive_checked64

theorem checked_primitive_binding :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
      Extracted.program Extracted.entryIndex := checked_primitive_contract

#print axioms checked_primitive_contract
#print axioms checked_primitive_binding

theorem checked_primitive_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex := checked_scalar_family checked_primitive_contract profile valid same

#print axioms checked_primitive_family

end UInt256Proof.Equality.Safety
