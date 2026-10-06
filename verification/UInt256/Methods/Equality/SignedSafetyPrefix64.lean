import UInt256.Methods.Equality.SignedSafetyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem signed_negative64 (right : BitVec 64) (negative : right.toInt < 0) :
    SignedNegative (.i64 right) := by
  equality_signed_negative negative

theorem signed_positive64 (right : BitVec 64) (nonnegative : ¬right.toInt < 0) :
    SignedPositive (.i64 right) := by
  equality_signed_positive nonnegative

#print axioms signed_negative64
#print axioms signed_positive64

end UInt256Proof.Equality.Safety
