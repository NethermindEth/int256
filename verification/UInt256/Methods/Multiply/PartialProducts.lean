import UInt256.Representation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Multiply

def retainedProducts (left right : Limbs) : Nat :=
  (left 0).toNat * (right 0).toNat +
  ((left 0).toNat * (right 1).toNat + (left 1).toNat * (right 0).toNat) * 2^64 +
  ((left 0).toNat * (right 2).toNat + (left 1).toNat * (right 1).toNat +
    (left 2).toNat * (right 0).toNat) * 2^128 +
  ((left 0).toNat * (right 3).toNat + (left 1).toNat * (right 2).toNat +
    (left 2).toNat * (right 1).toNat + (left 3).toNat * (right 0).toNat) * 2^192

theorem polynomial_split (a0 a1 a2 a3 b0 b1 b2 b3 radix : Nat) :
    (a0 + a1*radix + a2*radix^2 + a3*radix^3) *
      (b0 + b1*radix + b2*radix^2 + b3*radix^3) =
      a0*b0 + (a0*b1+a1*b0)*radix + (a0*b2+a1*b1+a2*b0)*radix^2 +
      (a0*b3+a1*b2+a2*b1+a3*b0)*radix^3 +
      ((a1*b3+a2*b2+a3*b1)+(a2*b3+a3*b2)*radix+a3*b3*radix^2)*radix^4 := by
  grind

theorem retained_products_correct (left right : Limbs) :
    (value left * value right).toNat = retainedProducts left right % 2^256 := by
  have polynomial := polynomial_split
    (left 0).toNat (left 1).toNat (left 2).toNat (left 3).toNat
    (right 0).toNat (right 1).toNat (right 2).toNat (right 3).toNat (2^64)
  simp (config := { implicitDefEqProofs := false }) only [show ((2 : Nat)^64)^2 = 2^128 by rw [← Nat.pow_mul],
    show ((2 : Nat)^64)^3 = 2^192 by rw [← Nat.pow_mul],
    show ((2 : Nat)^64)^4 = 2^256 by rw [← Nat.pow_mul]] at polynomial
  simp (config := { implicitDefEqProofs := false }) only
    [value, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod, Nat.mul_mod_mod]
  apply Eq.trans (congrArg (fun n : Nat => n % 2^256) polynomial)
  change (retainedProducts left right + _ * 2^256) % 2^256 = _
  exact Nat.add_mul_mod_self_right _ _ _

theorem retained_products_value (left right : Limbs) :
    value left * value right = BitVec.ofNat 256 (retainedProducts left right) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact retained_products_correct left right

end UInt256Proof.Multiply



#print axioms UInt256Proof.Multiply.retained_products_value
