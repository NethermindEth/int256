import UInt256.RepresentationLemmas

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Compare

/-- A limb contributes the native comparison's equality/greater-than base-four digit. -/
def orderingDigit (left right : W64) : Nat :=
  if left = right then 1 else if right.toNat < left.toNat then 2 else 0

def orderingMask (left right : Limbs) : Nat :=
  orderingDigit (left 0) (right 0) + 4 * orderingDigit (left 1) (right 1) +
    16 * orderingDigit (left 2) (right 2) + 64 * orderingDigit (left 3) (right 3)

private theorem digit_le (left right : W64) : orderingDigit left right ≤ 2 := by
  unfold orderingDigit
  split
  · omega
  · split <;> omega

private theorem digit_spec (left right : W64) :
    (orderingDigit left right = 0 ∧ left.toNat < right.toNat) ∨
    (orderingDigit left right = 1 ∧ left.toNat = right.toNat) ∨
    (orderingDigit left right = 2 ∧ right.toNat < left.toNat) := by
  unfold orderingDigit
  by_cases equal : left = right
  · exact Or.inr (Or.inl ⟨ite_eq_left equal, congrArg BitVec.toNat equal⟩)
  · have different : left.toNat ≠ right.toNat := fun same => equal (BitVec.eq_of_toNat_eq same)
    rw [ite_eq_right equal]
    by_cases greater : right.toNat < left.toNat
    · exact Or.inr (Or.inr ⟨ite_eq_left greater, greater⟩)
    · exact Or.inl ⟨ite_eq_right greater, by omega⟩

private theorem value_lt_iff (left right : Limbs) :
    (value left).toNat < (value right).toNat ↔
      (left 3).toNat < (right 3).toNat ∨ ((left 3).toNat = (right 3).toNat ∧
      ((left 2).toNat < (right 2).toNat ∨ ((left 2).toNat = (right 2).toNat ∧
      ((left 1).toNat < (right 1).toNat ∨ ((left 1).toNat = (right 1).toNat ∧
      (left 0).toNat < (right 0).toNat))))) := by
  rw [value_toNat, value_toNat]
  have := (left 0).isLt; have := (left 1).isLt; have := (left 2).isLt; have := (left 3).isLt
  have := (right 0).isLt; have := (right 1).isLt; have := (right 2).isLt; have := (right 3).isLt
  omega

private theorem value_le_iff (left right : Limbs) :
    (value left).toNat ≤ (value right).toNat ↔
      (left 3).toNat < (right 3).toNat ∨ ((left 3).toNat = (right 3).toNat ∧
      ((left 2).toNat < (right 2).toNat ∨ ((left 2).toNat = (right 2).toNat ∧
      ((left 1).toNat < (right 1).toNat ∨ ((left 1).toNat = (right 1).toNat ∧
      (left 0).toNat ≤ (right 0).toNat))))) := by
  rw [value_toNat, value_toNat]
  have := (left 0).isLt; have := (left 1).isLt; have := (left 2).isLt; have := (left 3).isLt
  have := (right 0).isLt; have := (right 1).isLt; have := (right 2).isLt; have := (right 3).isLt
  omega

theorem orderingMask_bound (left right : Limbs) : orderingMask left right ≤ 170 := by
  unfold orderingMask
  have := digit_le (left 0) (right 0); have := digit_le (left 1) (right 1)
  have := digit_le (left 2) (right 2); have := digit_le (left 3) (right 3)
  omega

theorem orderingMask_lt (left right : Limbs) :
    orderingMask left right < 85 ↔ (value left).toNat < (value right).toNat := by
  rw [value_lt_iff]
  unfold orderingMask
  have := digit_le (left 0) (right 0); have := digit_le (left 1) (right 1)
  have := digit_le (left 2) (right 2)
  rcases digit_spec (left 3) (right 3) with ⟨h3, c3⟩ | ⟨h3, c3⟩ | ⟨h3, c3⟩
  · omega
  · rcases digit_spec (left 2) (right 2) with ⟨h2, c2⟩ | ⟨h2, c2⟩ | ⟨h2, c2⟩
    · omega
    · rcases digit_spec (left 1) (right 1) with ⟨h1, c1⟩ | ⟨h1, c1⟩ | ⟨h1, c1⟩
      · omega
      · rcases digit_spec (left 0) (right 0) with ⟨h0, c0⟩ | ⟨h0, c0⟩ | ⟨h0, c0⟩ <;> omega
      · omega
    · omega
  · omega

theorem orderingMask_le (left right : Limbs) :
    orderingMask left right < 86 ↔ (value left).toNat ≤ (value right).toNat := by
  rw [value_le_iff]
  unfold orderingMask
  have := digit_le (left 0) (right 0); have := digit_le (left 1) (right 1)
  have := digit_le (left 2) (right 2)
  rcases digit_spec (left 3) (right 3) with ⟨h3, c3⟩ | ⟨h3, c3⟩ | ⟨h3, c3⟩
  · omega
  · rcases digit_spec (left 2) (right 2) with ⟨h2, c2⟩ | ⟨h2, c2⟩ | ⟨h2, c2⟩
    · omega
    · rcases digit_spec (left 1) (right 1) with ⟨h1, c1⟩ | ⟨h1, c1⟩ | ⟨h1, c1⟩
      · omega
      · rcases digit_spec (left 0) (right 0) with ⟨h0, c0⟩ | ⟨h0, c0⟩ | ⟨h0, c0⟩ <;> omega
      · omega
    · omega
  · omega

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

private theorem flag_le (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by
  split <;> omega

private theorem flags_spec (left right : W64) :
    ((if left = right then 1 else 0) = 1 ∧ (if left.toNat < right.toNat then 1 else 0) = 0 ∧
      left.toNat = right.toNat) ∨
    ((if left = right then 1 else 0) = 0 ∧ (if left.toNat < right.toNat then 1 else 0) = 1 ∧
      left.toNat < right.toNat) ∨
    ((if left = right then 1 else 0) = 0 ∧ (if left.toNat < right.toNat then 1 else 0) = 0 ∧
      right.toNat < left.toNat) := by
  by_cases equal : left = right
  · have same := congrArg BitVec.toNat equal
    exact Or.inl ⟨ite_eq_left equal, ite_eq_right (by omega), same⟩
  · have different : left.toNat ≠ right.toNat := fun same => equal (BitVec.eq_of_toNat_eq same)
    by_cases less : left.toNat < right.toNat
    · exact Or.inr (Or.inl ⟨ite_eq_right equal, ite_eq_left less, less⟩)
    · exact Or.inr (Or.inr ⟨ite_eq_right equal, ite_eq_right less, by omega⟩)

private theorem flags_le (left right : W64) :
    (if left = right then 1 else 0) + (if left.toNat < right.toNat then 1 else 0) ≤ 1 := by
  rcases flags_spec left right with ⟨e, l, _⟩ | ⟨e, l, _⟩ | ⟨e, l, _⟩ <;> omega

theorem equalityMask_bound (left right : Limbs) : equalityMask left right ≤ 15 := by
  unfold equalityMask
  have := flag_le (left 0 = right 0); have := flag_le (left 1 = right 1)
  have := flag_le (left 2 = right 2); have := flag_le (left 3 = right 3)
  omega

theorem lessMask_bound (left right : Limbs) : lessMask left right ≤ 15 := by
  unfold lessMask
  have := flag_le ((left 0).toNat < (right 0).toNat); have := flag_le ((left 1).toNat < (right 1).toNat)
  have := flag_le ((left 2).toNat < (right 2).toNat); have := flag_le ((left 3).toNat < (right 3).toNat)
  omega

theorem masks_sum_lt (left right : Limbs) :
    15 < equalityMask left right + 2 * lessMask left right ↔
      (value left).toNat < (value right).toNat := by
  rw [value_lt_iff]
  unfold equalityMask lessMask
  have := flags_le (left 0) (right 0); have := flags_le (left 1) (right 1)
  have := flags_le (left 2) (right 2)
  rcases flags_spec (left 3) (right 3) with ⟨e3, l3, c3⟩ | ⟨e3, l3, c3⟩ | ⟨e3, l3, c3⟩
  · rcases flags_spec (left 2) (right 2) with ⟨e2, l2, c2⟩ | ⟨e2, l2, c2⟩ | ⟨e2, l2, c2⟩
    · rcases flags_spec (left 1) (right 1) with ⟨e1, l1, c1⟩ | ⟨e1, l1, c1⟩ | ⟨e1, l1, c1⟩
      · rcases flags_spec (left 0) (right 0) with ⟨e0, l0, c0⟩ | ⟨e0, l0, c0⟩ | ⟨e0, l0, c0⟩ <;> omega
      · omega
      · omega
    · omega
    · omega
  · omega
  · omega

end UInt256Proof.Compare
