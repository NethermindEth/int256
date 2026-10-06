import UInt256.Methods.Multiply.EntrySafetyPrepared
import UInt256.Methods.Multiply.SingleWord
import UInt256.Safety.HalfRepresentation
import UInt256.Safety.PrivateInputValues

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem input_upper_zero (memory : Memory) (input : Reference)
    (zero : inputUpper memory input = 0) :
    inputLimb memory input 2 = 0 ∧ inputLimb memory input 3 = 0 :=
  BitVec.or_eq_zero_iff.mp zero

theorem input_tail_single (memory : Memory) (input : Reference)
    (zero : inputTail memory input = 0) :
    inputValue memory input = BitVec.ofNat 256 (inputLimb memory input 0).toNat := by
  have limbs := singleWord_eq (inputLimb memory input) zero
  exact (input_limbs_value memory input).symm.trans
    ((congrArg UInt256Model.value limbs.symm).trans (singleWord_value (inputLimb memory input 0)))

theorem small_product_value (memory : Memory) (left right : Reference)
    (leftSmall : inputTail memory left = 0) (rightSmall : inputTail memory right = 0) :
    BitVec.ofNat 256 ((lowProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat +
      (highProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat * 2^64) =
      inputValue memory left * inputValue memory right := by
  rw [input_tail_single memory left leftSmall, input_tail_single memory right rightSmall]
  rw [← BitVec.ofNat_mul]
  apply congrArg (BitVec.ofNat 256)
  rw [Nat.mul_comm (highProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat]
  exact product_decomposition (inputLimb memory left 0) (inputLimb memory right 0)

#print axioms input_upper_zero
#print axioms input_tail_single
#print axioms small_product_value
end UInt256Proof.Multiply.Safety
