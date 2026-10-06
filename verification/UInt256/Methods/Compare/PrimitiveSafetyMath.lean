import UInt256.Methods.Compare.Lemmas

namespace UInt256Proof.Compare.PrimitiveSafety
open UInt256Model

def predicate (signed scalarFirst : Bool) (input : BitVec 256) (word : BitVec 64) : Bool :=
  let number : Int := if signed then word.toInt else word.toNat
  decide (if scalarFirst then number < (input.toNat : Int) else (input.toNat : Int) < number)

theorem limbs_result_math (signed scalarFirst : Bool) (a : Limbs) (word : BitVec 64) :
    (if signed && decide (word.toInt < 0) then if scalarFirst then (1 : BitVec 32) else 0
     else if a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 then
       if (if scalarFirst then word.toNat < (a 0).toNat else (a 0).toNat < word.toNat) then 1 else 0
     else if scalarFirst then 1 else 0) =
      if predicate signed scalarFirst (value a) word then 1 else 0 := by
  have total := UInt256Proof.Equality.value_toNat a
  have bound := word.isLt
  have low := (a 0).isLt
  have nonnegative : 0 ≤ ((value a).toNat : Int) := Int.natCast_nonneg _
  have signedValue : ¬word.toInt < 0 → word.toInt = (word.toNat : Int) := by
    intro h
    have formula := BitVec.toInt_eq_toNat_cond word
    split at formula <;> omega
  have zeros : (a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0) ↔
      (a 1).toNat = 0 ∧ (a 2).toNat = 0 ∧ (a 3).toNat = 0 := by
    simp only [← BitVec.toNat_inj]
    rfl
  cases signed <;> cases scalarFirst <;>
    by_cases negative : word.toInt < 0 <;>
    by_cases upper : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0
  all_goals
    simp only [predicate, upper, negative, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      decide_true, decide_false, ite_true, ite_false,
      and_true, decide_eq_true_eq]
    rw [zeros] at upper
    repeat' first | rfl | split
    all_goals (have same := signedValue; omega)

#print axioms limbs_result_math
end UInt256Proof.Compare.PrimitiveSafety
