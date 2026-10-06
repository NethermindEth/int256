import UInt256.Methods.Equality.PrimitiveSafetyPrefix

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem primitive_prefix64 (right : BitVec 64) :
    PrimitivePrefix (.i64 right) right := by
  equality_primitive_prefix

#print axioms primitive_prefix64

end UInt256Proof.Equality.Safety
