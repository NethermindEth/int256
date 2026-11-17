import UInt256.Representation

open CIL

namespace UInt256Proof.Multiply

def lowProduct (left right : W64) : W64 := left * right

def highProduct (left right : W64) : W64 :=
  BitVec.ofNat 64 (left.toNat * right.toNat / 2^64)

theorem product_bound (left right : W64) : left.toNat * right.toNat < 2^64 * 2^64 := by
  have lower := Nat.mul_le_mul_right right.toNat (Nat.le_of_lt left.isLt)
  have upper := Nat.mul_lt_mul_of_pos_left right.isLt (show 0 < 2^64 by decide)
  exact Nat.lt_of_le_of_lt lower upper

theorem highProduct_bound (left right : W64) : left.toNat * right.toNat / 2^64 < 2^64 := by
  have bound := product_bound left right
  exact (Nat.div_lt_iff_lt_mul (by decide)).mpr bound

theorem highProduct_nat (left right : W64) :
    (highProduct left right).toNat = left.toNat * right.toNat / 2^64 := by
  exact Nat.mod_eq_of_lt (highProduct_bound left right)

theorem product_decomposition (left right : W64) :
    (lowProduct left right).toNat + 2^64 * (highProduct left right).toNat =
      left.toNat * right.toNat := by
  rw [highProduct_nat]
  simp only [lowProduct, BitVec.toNat_mul]
  exact Nat.mod_add_div _ _

end UInt256Proof.Multiply
