import UInt256.Methods.Equality.PrimitiveSafetyPrefix

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem primitive_prefix32 (right : BitVec 32) :
    PrimitivePrefix (.i32 right) (right.zeroExtend 64) := by
  equality_primitive_prefix

#print axioms primitive_prefix32

end UInt256Proof.Equality.Safety
