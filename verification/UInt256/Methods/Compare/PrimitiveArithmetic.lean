import UInt256.Methods.Compare.Lemmas

namespace UInt256Proof.Compare.PrimitiveSafety
open UInt256Model

def predicate (signed scalarFirst : Bool) (input : BitVec 256) (word : BitVec 64) : Bool :=
  let number : Int := if signed then word.toInt else word.toNat
  decide (if scalarFirst then number < (input.toNat : Int) else (input.toNat : Int) < number)

set_option maxRecDepth 8192
theorem signed_nonnegative (word : BitVec 64) (h : ¬word.toInt < 0) :
    word.toInt = (word.toNat : Int) := by
  have formula := BitVec.toInt_eq_toNat_cond word
  split at formula <;> omega

theorem upper_zeros (a : Limbs) : (a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0) ↔
    (a 1).toNat = 0 ∧ (a 2).toNat = 0 ∧ (a 3).toNat = 0 := by
  simp only [← BitVec.toNat_inj]
  rfl

theorem small_value (a : Limbs) (h : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0) :
    (value a).toNat = (a 0).toNat := by
  have total := UInt256Proof.Equality.value_toNat a
  rw [upper_zeros] at h
  omega

theorem large_value (a : Limbs) (word : BitVec 64) (h : ¬(a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0)) :
    word.toNat < (value a).toNat := by
  have total := UInt256Proof.Equality.value_toNat a
  have bound := word.isLt
  rw [upper_zeros] at h
  omega

theorem comparison_result {α : Type} (zero one : α) (signed first : Bool)
    (value low word : Nat) (signedWord : Int) (upper : Prop) [Decidable upper]
    (small : upper → value = low) (large : ¬upper → word < value)
    (nonnegative : ¬signedWord < 0 → signedWord = (word : Int)) :
    (if signed && decide (signedWord < 0) then if first then one else zero
     else if upper then
       if (if first then word < low else low < word) then one else zero
     else if first then one else zero) =
    (if decide (if first then (if signed then signedWord else (word : Int)) < (value : Int)
               else (value : Int) < (if signed then signedWord else (word : Int))) then one else zero) := by
  cases signed <;> cases first <;>
    by_cases negative : signedWord < 0 <;> by_cases high : upper
  all_goals
    first | have size := small high | have size := large high
    try have same := nonnegative negative
    simp only [high, negative, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      decide_true, decide_false, ite_true, ite_false, and_true, decide_eq_true_eq]
    repeat' first | rfl | split
    all_goals omega

theorem limbs_result_math (signed scalarFirst : Bool) (a : Limbs) (word : BitVec 64) :
    (if signed && decide (word.toInt < 0) then if scalarFirst then (1 : BitVec 32) else 0
     else if a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 then
       if (if scalarFirst then word.toNat < (a 0).toNat else (a 0).toNat < word.toNat) then 1 else 0
     else if scalarFirst then 1 else 0) =
      if predicate signed scalarFirst (value a) word then 1 else 0 := by
  exact comparison_result (0 : BitVec 32) 1 signed scalarFirst
    (value a).toNat (a 0).toNat word.toNat word.toInt
    (a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0)
    (small_value a) (large_value a word) (signed_nonnegative word)

#print axioms limbs_result_math
end UInt256Proof.Compare.PrimitiveSafety
