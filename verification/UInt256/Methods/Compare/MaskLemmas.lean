import UInt256.RepresentationLemmas

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Compare

/-- A limb contributes the native comparison's equality/greater-than base-four digit. -/
def orderingDigit (left right : W64) : Nat :=
  if left = right then 1 else if right.toNat < left.toNat then 2 else 0

def orderingMask (left right : Limbs) : Nat :=
  orderingDigit (left 0) (right 0) + 4 * orderingDigit (left 1) (right 1) +
    16 * orderingDigit (left 2) (right 2) + 64 * orderingDigit (left 3) (right 3)

theorem orderingMask_bound (left right : Limbs) : orderingMask left right ≤ 170 := by
  unfold orderingMask orderingDigit
  repeat' split
  all_goals omega

theorem orderingMask_lt (left right : Limbs) :
    orderingMask left right < 85 ↔ (value left).toNat < (value right).toNat := by
  rw [value_toNat,value_toNat]
  unfold orderingMask orderingDigit
  repeat' (split <;> try simp_all only [←BitVec.toNat_inj])
  all_goals omega

theorem orderingMask_le (left right : Limbs) :
    orderingMask left right < 86 ↔ (value left).toNat ≤ (value right).toNat := by
  rw [value_toNat,value_toNat]
  unfold orderingMask orderingDigit
  repeat' (split <;> try simp_all only [←BitVec.toNat_inj])
  all_goals omega

theorem mask_sub_negative (number bias : Nat) (numberBound : number ≤ 170)
    (biasPositive : 0 < bias) (biasBound : bias ≤ 86) :
    (BitVec.ofNat 32 number - BitVec.ofNat 32 bias).toInt < 0 ↔ number < bias := by
  simp only [BitVec.toInt_eq_toNat_cond,BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

theorem mask_toInt (number : Nat) (bound : number ≤ 170) :
    (BitVec.ofNat 32 number).toInt = (number : Int) := by
  simp only [BitVec.toInt_eq_toNat_cond,BitVec.toNat_ofNat]
  omega

theorem mask_sub_toInt (number bias : Nat) (bound : number ≤ 170)
    (biasBound : bias ≤ 86) :
    ((BitVec.ofNat 32 number).toInt - (bias : Int)).bmod 4294967296 =
      (number : Int) - (bias : Int) := by
  rw [mask_toInt number bound]
  exact Int.bmod_eq_of_le (by omega) (by omega)

def equalityMask (left right : Limbs) : Nat :=
  (if left 0 = right 0 then 1 else 0) + 2 * (if left 1 = right 1 then 1 else 0) +
    4 * (if left 2 = right 2 then 1 else 0) + 8 * (if left 3 = right 3 then 1 else 0)

def lessMask (left right : Limbs) : Nat :=
  (if (left 0).toNat < (right 0).toNat then 1 else 0) +
    2 * (if (left 1).toNat < (right 1).toNat then 1 else 0) +
    4 * (if (left 2).toNat < (right 2).toNat then 1 else 0) +
    8 * (if (left 3).toNat < (right 3).toNat then 1 else 0)

theorem equalityMask_bound (left right : Limbs) : equalityMask left right ≤ 15 := by
  unfold equalityMask
  repeat' split
  all_goals omega

theorem lessMask_bound (left right : Limbs) : lessMask left right ≤ 15 := by
  unfold lessMask
  repeat' split
  all_goals omega

theorem masks_sum_lt (left right : Limbs) :
    15 < equalityMask left right + 2 * lessMask left right ↔
      (value left).toNat < (value right).toNat := by
  rw [value_toNat,value_toNat]
  unfold equalityMask lessMask
  repeat' (split <;> try simp_all only [←BitVec.toNat_inj])
  all_goals omega

end UInt256Proof.Compare
