import UInt256.RepresentationLemmas
import UInt256.Methods.Multiply.Packing
open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem product_limbs_correct (a b : Limbs) : value (productLimbs a b) = value a * value b := by
  have reduced : productTotal a b % 2^256 = retainedProducts a b % 2^256 :=
    (Nat.add_mul_mod_self_right (productTotal a b) (productDiscarded a b) (2^256)).symm.trans
      (congrArg (fun n : Nat => n % 2^256) (product_conservation a b))
  have equal : BitVec.ofNat 256 (productTotal a b) = BitVec.ofNat 256 (retainedProducts a b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    exact reduced
  exact (productLimbs_value a b).trans (equal.trans (retained_products_value a b).symm)

theorem productLimbs_comm (a b : Limbs) : productLimbs a b = productLimbs b a := by
  apply representation_injective
  rw [product_limbs_correct, product_limbs_correct, BitVec.mul_comm]

end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.product_limbs_correct
