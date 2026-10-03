import UInt256.Methods.Multiply.Product
open CIL
namespace UInt256Proof.Multiply

def sumHigh (a b : W64) : W64 := BitVec.ofNat 64 ((a.toNat + b.toNat) / 2^64)
def countCarry (a b count : W64) : W64 := count + sumHigh a b

theorem sumHigh_nat (a b : W64) :
    (sumHigh a b).toNat = (a.toNat + b.toNat) / 2^64 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [sumHigh, BitVec.toNat_ofNat]
  omega

theorem sumHigh_bound (a b : W64) : (sumHigh a b).toNat ≤ 1 := by
  rw [sumHigh_nat]
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem sumHigh_flag (a b : W64) :
    (if a + b < a then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) = sumHigh a b := by
  apply BitVec.eq_of_toNat_eq
  rw [sumHigh_nat]
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem sum_decomposition (a b : W64) :
    (a + b).toNat + 2^64 * (sumHigh a b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, sumHigh_nat]
  exact Nat.mod_add_div _ _

theorem countCarry_nat (a b count : W64) (bound : count.toNat + 1 < 2^64) :
    (countCarry a b count).toNat = count.toNat + (sumHigh a b).toNat := by
  have high := sumHigh_bound a b
  simp only [countCarry, BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)
end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.sum_decomposition
