import UInt256.RepresentationLemmas

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

@[simp] theorem extend_subtract_choice (p : Prop) [Decidable p] :
    (if p then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64 =
      if p then BitVec.ofNat 64 1 else BitVec.ofNat 64 0 := by
  split <;> rfl


@[irreducible] def borrow (x y c : W64) : W64 :=
  if x.toNat < y.toNat + c.toNat then 1 else 0

theorem borrow_bound (x y c : W64) : (borrow x y c).toNat ≤ 1 := by
  unfold borrow
  split <;> decide

theorem borrow_word_nat (x y c : W64) (hc : c.toNat ≤ 1) :
    x.toNat + 2^64 * (borrow x y c).toNat =
      y.toNat + c.toNat + (x - y - c).toNat := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [borrow, BitVec.toNat_sub]
  split <;> simp <;> omega

theorem borrow_expression (x y c : W64) (hc : c.toNat ≤ 1) :
    (if x < y then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) |||
      (c &&& (if x = y then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) = borrow x y c := by
  have hx := x.isLt
  have hy := y.isLt
  have hz : c = 0 ∨ c = 1 := by
    have hn : c.toNat = 0 ∨ c.toNat = 1 := by omega
    rcases hn with hn | hn
    · left; apply BitVec.eq_of_toNat_eq; simpa using hn
    · right; apply BitVec.eq_of_toNat_eq; simpa using hn
  rcases hz with rfl | rfl
  all_goals by_cases hxy : x < y <;> by_cases he : x = y
  all_goals simp only [borrow, hxy, he, ↓reduceIte]
  all_goals simp [BitVec.lt_def, BitVec.toNat_eq] at hxy he ⊢
  all_goals omega

theorem borrow_alternative_expression (x y c : W64) (hc : c.toNat ≤ 1) :
    (if x < y then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) +
      (if x - y < c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) = borrow x y c := by
  have hx := x.isLt
  have hy := y.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [borrow, BitVec.toNat_add, BitVec.lt_def, BitVec.toNat_sub]
  split <;> split <;> split <;> simp <;> omega

theorem borrow_initial (x y : W64) :
    borrow x y 0 = if x < y then 1 else 0 := by
  simp [borrow, BitVec.lt_def]

theorem borrow_initial_flag (x y : W64) :
    borrow x y (BitVec.ofNat 64 0) =
      if x < y then BitVec.ofNat 64 1 else BitVec.ofNat 64 0 := by
  exact borrow_initial x y

theorem borrow_flag_fold (x y : W64) :
    (if x < y then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) =
      borrow x y (BitVec.ofNat 64 0) := (borrow_initial_flag x y).symm

theorem borrow_flags_or (x y c : W64) (hc : c.toNat ≤ 1) :
    borrow x y (BitVec.ofNat 64 0) |||
      (c &&& (if x = y then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) = borrow x y c := by
  rw [borrow_initial_flag]
  exact borrow_expression x y c hc

theorem borrow_flags_add (x y c : W64) (hc : c.toNat ≤ 1) :
    borrow x y (BitVec.ofNat 64 0) + borrow (x - y) c (BitVec.ofNat 64 0) = borrow x y c := by
  rw [borrow_initial_flag, borrow_initial_flag]
  exact borrow_alternative_expression x y c hc

theorem borrow_zero_right (x c : W64) (hc : c.toNat ≤ 1) :
    borrow x 0 c = if x = 0 then c else 0 := by
  have hx := x.isLt
  by_cases hz : x = 0
  · subst x
    have hn : c.toNat = 0 ∨ c.toNat = 1 := by omega
    rcases hn with hn | hn
    all_goals apply BitVec.eq_of_toNat_eq
    all_goals simp [borrow, hn]
  · have hn : x.toNat ≠ 0 := by
      intro he
      exact hz (BitVec.eq_of_toNat_eq (by simpa using he))
    have hnot : ¬ x.toNat < c.toNat := by omega
    simp [borrow, hnot]
    intro he
    have heNat : x.toNat = 0 := by simpa using congrArg BitVec.toNat he
    exact False.elim (hn heNat)

@[simp] theorem borrow_zero_zero (x : W64) : borrow x 0 0 = 0 := by
  simp [borrow]

@[simp] theorem borrow_zero_one (x : W64) : borrow x 0 1 = if x = 0 then 1 else 0 := by
  exact borrow_zero_right x 1 (by decide)

-- The borrow chain is mathematical data; execution must establish these words.
def differenceWords (a b : Limbs) : Limbs :=
  let c1 := borrow (a 0) (b 0) 0
  let c2 := borrow (a 1) (b 1) c1
  let c3 := borrow (a 2) (b 2) c2
  fun i => if i.val = 0 then a 0 - b 0 else
    if i.val = 1 then a 1 - b 1 - c1 else
    if i.val = 2 then a 2 - b 2 - c2 else a 3 - b 3 - c3

private theorem borrow_congr2 (f : Nat → Nat → Nat) {a b c d : Nat}
    (h : a = b) (k : c = d) : f a c = f b d := by cases h; cases k; rfl

theorem borrow_telescope (a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 c1 c2 c3 c4 : Nat)
    (h0 : a0 + 2^64 * c1 = b0 + r0)
    (h1 : a1 + 2^64 * c2 = b1 + c1 + r1)
    (h2 : a2 + 2^64 * c3 = b2 + c2 + r2)
    (h3 : a3 + 2^64 * c4 = b3 + c3 + r3) :
    a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192 + c4 * 2^256 =
      (b0 + b1 * 2^64 + b2 * 2^128 + b3 * 2^192) +
      (r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192) := by
  have sum01 := borrow_congr2 (fun x y : Nat => x + 2^64 * y) h0 h1
  have sum23 := borrow_congr2 (fun x y : Nat => 2^128 * x + 2^192 * y) h2 h3
  have summed := borrow_congr2 (fun x y : Nat => x + y) sum01 sum23
  clear h0 h1 h2 h3 sum01 sum23
  omega

theorem borrow_mod_total (r c a b : Nat) (h : a + c * 2^256 = b + r) :
    r % 2^256 = (2^256 - b % 2^256 + a % 2^256) % 2^256 := by omega

theorem four_limb_difference (a b : Limbs) :
    value (differenceWords a b) = value a - value b := by
  have hc0 : (0 : W64).toNat ≤ 1 := by decide
  have h0 := borrow_word_nat (a 0) (b 0) 0 hc0
  have h1 := borrow_word_nat (a 1) (b 1) _ (borrow_bound (a 0) (b 0) 0)
  have h2 := borrow_word_nat (a 2) (b 2) _
    (borrow_bound (a 1) (b 1) (borrow (a 0) (b 0) 0))
  have h3 := borrow_word_nat (a 3) (b 3) _
    (borrow_bound (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0)))
  change (a 0).toNat + 2^64 * (borrow (a 0) (b 0) 0).toNat =
    (b 0).toNat + (BitVec.ofNat 64 0).toNat + (a 0 - b 0 - BitVec.ofNat 64 0).toNat at h0
  simp only [BitVec.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at h0
  have total := borrow_telescope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [value, differenceWords, BitVec.toNat_ofNat,
    Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl, ↓reduceIte]
  exact borrow_mod_total _ _ _ _ total

theorem subtract_zero_word (x : W64) : x - (0 : W64) = x := by
  exact BitVec.sub_zero x

def smallDifference (a : Limbs) (b : W64) : Limbs := fun i =>
  if i.val = 0 then a 0 - b else
  if i.val = 1 then if a 0 < b then a 1 - 1 else a 1 else
  if i.val = 2 then if a 0 < b ∧ a 1 = 0 then a 2 - 1 else a 2 else
  if a 0 < b ∧ a 1 = 0 ∧ a 2 = 0 then a 3 - 1 else a 3

def subtractionSingleLimb (b : W64) : Limbs := fun i => if i.val = 0 then b else 0

theorem small_difference_words (a : Limbs) (b : W64) :
    smallDifference a b = differenceWords a (subtractionSingleLimb b) := by
  funext i
  simp only [differenceWords, subtractionSingleLimb, Fin.val_zero, Fin.val_one,
    Fin.val_two, show (3 : Fin 4).val = 3 from rfl, ↓reduceIte]
  simp only [show (1 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 0 from by decide,
    show (3 : Nat) ≠ 0 from by decide, ↓reduceIte]
  rw [borrow_initial]
  by_cases h0 : a 0 < b <;> by_cases h1 : a 1 = 0 <;> by_cases h2 : a 2 = 0
  all_goals simp only [smallDifference, h0, h1, h2, ↓reduceIte,
    borrow_zero_zero, borrow_zero_one, subtract_zero_word, and_true, and_false]

end UInt256Proof
