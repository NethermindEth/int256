import UInt256.Methods.Equality.Lemmas
import UInt256.Methods.Compare.Contract

open CIL UInt256Model
namespace UInt256Proof.Compare

/-- Unsigned ordering gives the highest differing limb precedence. -/
theorem value_lt_iff (a b : Limbs) : (value a).toNat < (value b).toNat ↔
    (a 3).toNat < (b 3).toNat ∨
    (a 3 = b 3 ∧ ((a 2).toNat < (b 2).toNat ∨
    (a 2 = b 2 ∧ ((a 1).toNat < (b 1).toNat ∨
    (a 1 = b 1 ∧ (a 0).toNat < (b 0).toNat))))) := by
  have ha0 := (a 0).isLt
  have ha1 := (a 1).isLt
  have ha2 := (a 2).isLt
  have ha3 := (a 3).isLt
  have hb0 := (b 0).isLt
  have hb1 := (b 1).isLt
  have hb2 := (b 2).isLt
  have hb3 := (b 3).isLt
  rw [Equality.value_toNat, Equality.value_toNat]
  simp only [← BitVec.toNat_inj]
  omega

/-- A short-circuit scalar ordering is justified by unsigned value order. -/
theorem value_lt_descending (a b : Limbs) :
    (value a).toNat < (value b).toNat ↔
      (if a 3 = b 3 then
        if a 2 = b 2 then
          if a 1 = b 1 then a 0 < b 0 else a 1 < b 1
        else a 2 < b 2
      else a 3 < b 3) := by
  rw [value_lt_iff]
  by_cases h3 : a 3 = b 3
  · by_cases h2 : a 2 = b 2
    · by_cases h1 : a 1 = b 1
      · simp [h3, h2, h1, BitVec.lt_def]
      · simp [h3, h2, h1, BitVec.lt_def]
    · simp [h3, h2, BitVec.lt_def]
  · simp [h3, BitVec.lt_def]

theorem compareWord_sign (left right : Nat) :
    UInt256Model.Compare.signAgreement (UInt256Model.Compare.compareWord left right)
      left right := by
  by_cases hlt : left < right
  · simp [UInt256Model.Compare.compareWord, UInt256Model.Compare.signAgreement, hlt]
    omega
  · by_cases heq : left = right
    · simp [UInt256Model.Compare.compareWord, UInt256Model.Compare.signAgreement, heq]
    · simp [UInt256Model.Compare.compareWord, UInt256Model.Compare.signAgreement, hlt, heq]
      omega

theorem exact_three_way_implies_sign (p : Program) (entry : Nat) (initial : Bytes)
    (left right : Nat)
    (exactResult : UInt256Model.Compare.ExactThreeWayContract p entry initial left right) :
    UInt256Model.Compare.ThreeWayContract p entry initial left right := by
  obtain ⟨fuel, final, execution, bytes⟩ := exactResult
  exact ⟨fuel, final, _, execution, compareWord_sign _ _, bytes⟩

/-- Any negative/positive result magnitudes meet the comparison API's promise. -/
theorem sign_magnitudes (negative positive : W32) (left right : Nat)
    (hn : negative.toInt < 0) (hp : 0 < positive.toInt) :
    UInt256Model.Compare.signAgreement
      (if left < right then negative else if left = right then 0 else positive)
      left right := by
  by_cases hlt : left < right
  · simp [UInt256Model.Compare.signAgreement, hlt]
    omega
  · by_cases heq : left = right
    · simp [UInt256Model.Compare.signAgreement, heq]
    · simp [UInt256Model.Compare.signAgreement, hlt, heq]
      omega

theorem signExtend32_toNat (word : W32) :
    (word.signExtend 64).toNat =
      if 2 * word.toNat < 4294967296 then word.toNat
      else word.toNat + 18446744069414584320 := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
    BitVec.msb_eq_decide]
  split <;> split <;> simp_all <;> omega

theorem zeroExtend32_toNat (word : W32) : (word.zeroExtend 64).toNat = word.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]

theorem zeroExtend32_toInt (word : W32) : (word.zeroExtend 64).toInt = (word.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond,zeroExtend32_toNat]
  have bound := word.isLt
  split <;> omega

@[simp high] theorem setWidth32_toInt (word : W32) : (word.setWidth 64).toInt = (word.toNat : Int) :=
  zeroExtend32_toInt word

theorem word32_bmod64 (word : W32) :
    (word.toNat : Int).bmod (2^64) = (word.toNat : Int) := by
  have bound := word.isLt
  apply Int.bmod_eq_of_le <;> omega

theorem word32_bmod64_nonnegative (word : W32) :
    ¬((word.toNat : Int).bmod (2^64) < 0) := by
  rw [word32_bmod64]
  omega

end UInt256Proof.Compare
