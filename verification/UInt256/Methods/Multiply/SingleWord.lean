import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ScalarValue
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

def singleWord (word : W64) : Limbs := fun i => if i = 0 then word else BitVec.ofNat 64 0

theorem singleWord_value (word : W64) : value (singleWord word) = BitVec.ofNat 256 word.toNat := by
  simp [value, singleWord]

theorem singleWord_eq (a : Limbs)
    (h : a 1 ||| (a 2 ||| a 3) = BitVec.ofNat 64 0) : singleWord (a 0) = a := by
  obtain ⟨h1, h23⟩ := BitVec.or_eq_zero_iff.mp h
  obtain ⟨h2, h3⟩ := BitVec.or_eq_zero_iff.mp h23
  funext i
  rcases i with ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h
  all_goals subst i; simp [singleWord, h1, h2, h3]

theorem productLimbs_single_right (a : Limbs) (word : W64) :
    productLimbs a (singleWord word) = scalarLimbs a word := by
  apply representation_injective
  rw [product_limbs_correct, scalar_limbs_correct, singleWord_value]

theorem productLimbs_single_left (word : W64) (a : Limbs) :
    productLimbs (singleWord word) a = scalarLimbs a word := by
  rw [productLimbs_comm, productLimbs_single_right]

theorem single_product_value (a b : W64) :
    value (fun i => if i = 0 then lowProduct a b else if i = 1 then highProduct a b else BitVec.ofNat 64 0) =
      value (singleWord a) * value (singleWord b) := by
  rw [singleWord_value, singleWord_value]
  have decomposition := product_decomposition a b
  simp (config := { implicitDefEqProofs := false }) only [value, Fin.isValue, ↓reduceIte, Fin.reduceEq, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
  rw [← BitVec.ofNat_mul]
  have equality : (lowProduct a b).toNat + (highProduct a b).toNat * 2^64 = a.toNat * b.toNat := by
    rw [Nat.mul_comm (highProduct a b).toNat]
    exact decomposition
  exact congrArg (BitVec.ofNat 256) equality

end UInt256Proof.Multiply
