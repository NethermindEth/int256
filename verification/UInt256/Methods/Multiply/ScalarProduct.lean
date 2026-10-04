import UInt256.Methods.Multiply.CountCarry
import UInt256.Methods.Multiply.PartialProducts
open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem highProduct_spare_bit (a b : W64) : (highProduct a b).toNat + 1 < 2^64 := by
  have bound : a.toNat * b.toNat ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)
  rw [highProduct_nat]
  omega

def scalarCarry (a b incoming : W64) : W64 := highProduct a b + sumHigh (lowProduct a b) incoming

theorem scalarCarry_nat (a b incoming : W64) :
    (scalarCarry a b incoming).toNat = (highProduct a b).toNat + (sumHigh (lowProduct a b) incoming).toNat := by
  have high := highProduct_spare_bit a b
  have flag := sumHigh_bound (lowProduct a b) incoming
  simp only [scalarCarry, BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

def scalarLimbs (a : Limbs) (word : W64) : Limbs := fun i =>
  if i.val = 0 then lowProduct word (a 0) else
  if i.val = 1 then lowProduct word (a 1) + highProduct word (a 0) else
  if i.val = 2 then lowProduct word (a 2) + scalarCarry word (a 1) (highProduct word (a 0)) else
    lowProduct word (a 3) + scalarCarry word (a 2) (scalarCarry word (a 1) (highProduct word (a 0)))

def scalarTotal (a : Limbs) (word : W64) : Nat :=
  (lowProduct word (a 0)).toNat + (lowProduct word (a 1) + highProduct word (a 0)).toNat * 2^64 +
    (lowProduct word (a 2) + scalarCarry word (a 1) (highProduct word (a 0))).toNat * 2^128 +
    (lowProduct word (a 3) + scalarCarry word (a 2)
      (scalarCarry word (a 1) (highProduct word (a 0)))).toNat * 2^192

def scalarRetained (a : Limbs) (word : W64) : Nat :=
  word.toNat * (a 0).toNat + word.toNat * (a 1).toNat * 2^64 +
    word.toNat * (a 2).toNat * 2^128 + word.toNat * (a 3).toNat * 2^192

theorem scalar_polynomial (a0 a1 a2 a3 word radix : Nat) :
    (a0 + a1*radix + a2*radix^2 + a3*radix^3) * word =
      word*a0 + word*a1*radix + word*a2*radix^2 + word*a3*radix^3 := by grind

def scalarDiscarded (a : Limbs) (word : W64) : Nat :=
  (highProduct word (a 3)).toNat +
    (sumHigh (lowProduct word (a 3)) (scalarCarry word (a 2)
      (scalarCarry word (a 1) (highProduct word (a 0))))).toNat

theorem scalar_conservation (a : Limbs) (word : W64) :
    scalarTotal a word + scalarDiscarded a word * 2^256 = scalarRetained a word := by
  have p0 := product_decomposition word (a 0)
  have p1 := product_decomposition word (a 1)
  have p2 := product_decomposition word (a 2)
  have p3 := product_decomposition word (a 3)
  have sum1 := sum_decomposition (lowProduct word (a 1)) (highProduct word (a 0))
  have sum2 := sum_decomposition (lowProduct word (a 2))
    (scalarCarry word (a 1) (highProduct word (a 0)))
  have sum3 := sum_decomposition (lowProduct word (a 3))
    (scalarCarry word (a 2) (scalarCarry word (a 1) (highProduct word (a 0))))
  have carry1 := scalarCarry_nat word (a 1) (highProduct word (a 0))
  have carry2 := scalarCarry_nat word (a 2) (scalarCarry word (a 1) (highProduct word (a 0)))
  simp only [scalarTotal, scalarDiscarded, scalarRetained]
  omega

end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.scalarCarry_nat
