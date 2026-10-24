import UInt256.Arithmetic.Carry
import UInt256.Arithmetic.Borrow
import UInt256.RepresentationLemmas

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192

namespace UInt256Proof.Reporting

theorem word_positive (x : W64) : BitVec.ofNat 64 0 < x ↔ x ≠ BitVec.ofNat 64 0 := by
  simp only [BitVec.lt_def, Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

def naturalValue (a : Limbs) : Nat :=
  (a 0).toNat + (a 1).toNat * 2^64 + (a 2).toNat * 2^128 + (a 3).toNat * 2^192

theorem naturalValue_bound (a : Limbs) : naturalValue a < 2^256 := by
  exact limbValue_bound a

theorem value_toNat (a : Limbs) : (value a).toNat = naturalValue a := by
  exact UInt256Proof.value_toNat a

def finalCarry (a b : Limbs) : W64 :=
  carry (a 3) (b 3) (carry (a 2) (b 2) (carry (a 1) (b 1) (carry (a 0) (b 0) 0)))

def finalBorrow (a b : Limbs) : W64 :=
  borrow (a 3) (b 3) (borrow (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0)))

theorem finalCarry_overflow (a b : Limbs) :
    finalCarry a b ≠ 0 ↔ 2^256 ≤ (value a).toNat + (value b).toNat := by
  have z : (0 : W64).toNat ≤ 1 := by decide
  have h0 := carry_word_nat (a 0) (b 0) 0 z
  have c1 := carry_bound (a 0) (b 0) 0 z
  have h1 := carry_word_nat (a 1) (b 1) _ c1
  have c2 := carry_bound (a 1) (b 1) _ c1
  have h2 := carry_word_nat (a 2) (b 2) _ c2
  have c3 := carry_bound (a 2) (b 2) _ c2
  have h3 := carry_word_nat (a 3) (b 3) _ c3
  change (a 0 + b 0 + BitVec.ofNat 64 0).toNat + 2^64 *
    (carry (a 0) (b 0) 0).toNat = (a 0).toNat + (b 0).toNat + (BitVec.ofNat 64 0).toNat at h0
  simp only [BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at h0
  have total := telescope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3
  have r0 := (a 0 + b 0 + (0 : W64)).isLt
  have r1 := (a 1 + b 1 + carry (a 0) (b 0) 0).isLt
  have r2 := (a 2 + b 2 + carry (a 1) (b 1) (carry (a 0) (b 0) 0)).isLt
  have r3 := (a 3 + b 3 + carry (a 2) (b 2) (carry (a 1) (b 1) (carry (a 0) (b 0) 0))).isLt
  rw [value_toNat, value_toNat]
  change finalCarry a b ≠ BitVec.ofNat 64 0 ↔ _
  simp only [finalCarry, naturalValue, Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem finalBorrow_underflow (a b : Limbs) :
    finalBorrow a b ≠ 0 ↔ (value a).toNat < (value b).toNat := by
  have z : (0 : W64).toNat ≤ 1 := by decide
  have h0 := borrow_word_nat (a 0) (b 0) 0 z
  have c1 := borrow_bound (a 0) (b 0) 0
  have h1 := borrow_word_nat (a 1) (b 1) _ c1
  have c2 := borrow_bound (a 1) (b 1) (borrow (a 0) (b 0) 0)
  have h2 := borrow_word_nat (a 2) (b 2) _ c2
  have c3 := borrow_bound (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0))
  have h3 := borrow_word_nat (a 3) (b 3) _ c3
  change (a 0).toNat + 2^64 * (borrow (a 0) (b 0) 0).toNat =
    (b 0).toNat + (BitVec.ofNat 64 0).toNat + (a 0 - b 0 - BitVec.ofNat 64 0).toNat at h0
  simp only [BitVec.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at h0
  have total := borrow_telescope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3
  have r0 := (a 0 - b 0 - (0 : W64)).isLt
  have r1 := (a 1 - b 1 - borrow (a 0) (b 0) 0).isLt
  have r2 := (a 2 - b 2 - borrow (a 1) (b 1) (borrow (a 0) (b 0) 0)).isLt
  have r3 := (a 3 - b 3 - borrow (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0))).isLt
  rw [value_toNat, value_toNat]
  change finalBorrow a b ≠ BitVec.ofNat 64 0 ↔ _
  simp only [finalBorrow, naturalValue, Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem small_overflow_iff (a : Limbs) (b : W64) :
    (a 0 + b < a 0 ∧ a 1 + 1 = 0 ∧ a 2 + 1 = 0 ∧ a 3 + 1 = 0) ↔
      2^256 ≤ (value a).toNat + (value (singleLimb b)).toNat := by
  rw [← finalCarry_overflow]
  by_cases h0 : a 0 + b < a 0 <;>
    by_cases h1 : a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases h3 : a 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
  all_goals simp [finalCarry, singleLimb, carry_zero, carry_one, h0, h1, h2, h3]

theorem small_underflow_iff (a : Limbs) (b : W64) :
    (a 0 < b ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0) ↔
      (value a).toNat < (value (singleLimb b)).toNat := by
  change (a 0 < b ∧ a 1 = BitVec.ofNat 64 0 ∧
    a 2 = BitVec.ofNat 64 0 ∧ a 3 = BitVec.ofNat 64 0) ↔ _
  simp [value_toNat, naturalValue, singleLimb, BitVec.lt_def, BitVec.toNat_eq]
  have hb := b.isLt
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  omega

end UInt256Proof.Reporting

#print axioms UInt256Proof.Reporting.finalCarry_overflow
#print axioms UInt256Proof.Reporting.finalBorrow_underflow
#print axioms UInt256Proof.Reporting.small_overflow_iff
#print axioms UInt256Proof.Reporting.small_underflow_iff
