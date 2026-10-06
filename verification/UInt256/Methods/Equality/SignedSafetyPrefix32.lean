import UInt256.Methods.Equality.SignedSafetyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem signed_negative32 (right : BitVec 32) (negative : right.toInt < 0) :
    SignedNegative (.i32 right) := by
  equality_signed_negative negative

theorem signed_positive32 (right : BitVec 32) (nonnegative : ¬right.toInt < 0) :
    SignedPositive (.i32 right) := by
  equality_signed_positive nonnegative

#print axioms signed_negative32
#print axioms signed_positive32

end UInt256Proof.Equality.Safety
