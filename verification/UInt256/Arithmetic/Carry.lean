import UInt256.Representation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

def carry (x y c : W64) : W64 :=
  (if x + y < x then 1 else 0) + (if x + y + c < x + y then 1 else 0)

-- Overflow can be detected by comparing the wrapped sum to either operand.
theorem add_overflow_right (x y : W64) : x + y < y ↔ x + y < x := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add]
  omega

@[simp] theorem extend_choice (p : Prop) [Decidable p] :
    (if p then (1 : W32) else 0).signExtend 64 = if p then (1 : W64) else 0 := by
  split <;> rfl
theorem carry_nat (x y c : W64) (hc : c.toNat ≤ 1) :
    (x + y + c).toNat + 2^64 *
      ((if x + y < x then 1 else 0) + (if x + y + c < x + y then 1 else 0)) =
        x.toNat + y.toNat + c.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add]
  split <;> split <;> omega

theorem carry_bound (x y c : W64) (hc : c.toNat ≤ 1) : (carry x y c).toNat ≤ 1 := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [carry, BitVec.lt_def, BitVec.toNat_add]
  split <;> split <;> simp <;> omega

theorem carry_word_nat (x y c : W64) (hc : c.toNat ≤ 1) :
    (x + y + c).toNat + 2^64 * (carry x y c).toNat = x.toNat + y.toNat + c.toNat := by
  have h := carry_nat x y c hc
  simp only [carry, BitVec.lt_def, BitVec.toNat_add] at h ⊢
  split <;> split <;> simp_all <;> omega

theorem congr2 (f : Nat → Nat → Nat) {a b c d : Nat} (h : a = b) (k : c = d) :
    f a c = f b d := by cases h; cases k; rfl

theorem telescope (a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 c1 c2 c3 c4 : Nat)
    (h0 : r0 + 2^64 * c1 = a0 + b0)
    (h1 : r1 + 2^64 * c2 = a1 + b1 + c1)
    (h2 : r2 + 2^64 * c3 = a2 + b2 + c2)
    (h3 : r3 + 2^64 * c4 = a3 + b3 + c3) :
    r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192 + c4 * 2^256 =
      (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192) +
      (b0 + b1 * 2^64 + b2 * 2^128 + b3 * 2^192) := by
  have sum01 := congr2 (fun x y : Nat => x + 2^64 * y) h0 h1
  have sum23 := congr2 (fun x y : Nat => 2^128 * x + 2^192 * y) h2 h3
  have summed := congr2 (fun x y : Nat => x + y) sum01 sum23
  clear h0 h1 h2 h3 sum01 sum23
  omega

theorem mod_total (r c a b : Nat) (h : r + c * 2^256 = a + b) :
    r % 2^256 = (a % 2^256 + b % 2^256) % 2^256 := by omega

-- Arithmetic lemma for the general path. The execution proof must still
-- establish that the imported instructions produce these intermediate values.
theorem four_limb_sum (a b : Limbs) :
    let c1 := carry (a 0) (b 0) 0
    let c2 := carry (a 1) (b 1) c1
    let c3 := carry (a 2) (b 2) c2
    value (fun i => if i.val = 0 then a 0 + b 0 else
      if i.val = 1 then a 1 + b 1 + c1 else
      if i.val = 2 then a 2 + b 2 + c2 else a 3 + b 3 + c3) = value a + value b := by
  dsimp only
  have hc0 : (0 : W64).toNat ≤ 1 := by decide
  have hc1 := carry_bound (a 0) (b 0) 0 hc0
  have hc2 := carry_bound (a 1) (b 1) _ hc1
  have hc3 := carry_bound (a 2) (b 2) _ hc2
  have h0 := carry_word_nat (a 0) (b 0) 0 hc0
  have h1 := carry_word_nat (a 1) (b 1) _ hc1
  have h2 := carry_word_nat (a 2) (b 2) _ hc2
  have h3 := carry_word_nat (a 3) (b 3) _ hc3
  change (a 0 + b 0 + BitVec.ofNat 64 0).toNat + 2^64 *
    (carry (a 0) (b 0) 0).toNat = (a 0).toNat + (b 0).toNat + (BitVec.ofNat 64 0).toNat at h0
  simp only [BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at h0
  let r0 := a 0 + b 0
  let r1 := a 1 + b 1 + carry (a 0) (b 0) 0
  let r2 := a 2 + b 2 + carry (a 1) (b 1) (carry (a 0) (b 0) 0)
  let r3 := a 3 + b 3 + carry (a 2) (b 2) (carry (a 1) (b 1) (carry (a 0) (b 0) 0))
  let c4 := carry (a 3) (b 3) (carry (a 2) (b 2) (carry (a 1) (b 1) (carry (a 0) (b 0) 0)))
  let av := (a 0).toNat + (a 1).toNat * 2^64 + (a 2).toNat * 2^128 + (a 3).toNat * 2^192
  let bv := (b 0).toNat + (b 1).toNat * 2^64 + (b 2).toNat * 2^128 + (b 3).toNat * 2^192
  have total : r0.toNat + r1.toNat * 2^64 + r2.toNat * 2^128 + r3.toNat * 2^192 +
      c4.toNat * 2^256 = av + bv := by
    exact telescope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp only [value, BitVec.toNat_ofNat,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
    ↓reduceIte]
  exact mod_total _ _ _ _ total

def singleLimb (b : W64) : Limbs := fun i => if i.val = 0 then b else 0

theorem singleLimb_eq (a : Limbs) (h1 : a 1 = 0) (h2 : a 2 = 0) (h3 : a 3 = 0) :
    singleLimb (a 0) = a := by
  funext i
  rcases i with ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h
  all_goals subst i; simp [singleLimb, h1, h2, h3]

def smallResult (a : Limbs) (b : W64) : Limbs := fun i =>
  if i.val = 0 then a 0 + b else
  if i.val = 1 then if a 0 + b < a 0 then a 1 + 1 else a 1 else
  if i.val = 2 then if a 0 + b < a 0 ∧ a 1 + 1 = 0 then a 2 + 1 else a 2 else
  if a 0 + b < a 0 ∧ a 1 + 1 = 0 ∧ a 2 + 1 = 0 then a 3 + 1 else a 3

theorem increment_lt (x : W64) : x + 1 < x ↔ x + 1 = 0 := by
  have hx := x.isLt
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.lt_def, BitVec.toNat_add] at h
    change (x.toNat + 1) % 2^64 < x.toNat at h
    simp only [BitVec.toNat_add]
    change (x.toNat + 1) % 2^64 = 0
    omega
  · intro h
    have he := congrArg BitVec.toNat h
    simp only [BitVec.lt_def, BitVec.toNat_add]
    change (x.toNat + 1) % 2^64 < x.toNat
    change (x.toNat + 1) % 2^64 = 0 at he
    omega

theorem carry_zero (x y : W64) : carry x y (BitVec.ofNat 64 0) =
    if x + y < x then BitVec.ofNat 64 1 else BitVec.ofNat 64 0 := by
  simp [carry]

theorem carry_one (x : W64) : carry x (BitVec.ofNat 64 0) (BitVec.ofNat 64 1) =
    if x + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 then BitVec.ofNat 64 1 else BitVec.ofNat 64 0 := by
  have hi : x + BitVec.ofNat 64 1 < x ↔ x + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 := increment_lt x
  simp [carry, hi]

theorem small_result_sum (a : Limbs) (b : W64) :
    value (smallResult a b) = value a + value (singleLimb b) := by
  have h := four_limb_sum a (singleLimb b)
  dsimp only at h
  have shape : (fun i : Fin 4 => if i.val = 0 then a 0 + singleLimb b 0 else
      if i.val = 1 then a 1 + singleLimb b 1 + carry (a 0) (singleLimb b 0) 0 else
      if i.val = 2 then a 2 + singleLimb b 2 +
        carry (a 1) (singleLimb b 1) (carry (a 0) (singleLimb b 0) 0) else
        a 3 + singleLimb b 3 + carry (a 2) (singleLimb b 2)
          (carry (a 1) (singleLimb b 1) (carry (a 0) (singleLimb b 0) 0))) = smallResult a b := by
    by_cases hc : a 0 + b < a 0 <;>
      by_cases h1 : a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
      by_cases h2 : a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
    all_goals
      funext i
      simp [smallResult, singleLimb, carry_zero, carry_one, hc, h1, h2,
        show (3 : Fin 4).val = 3 from rfl]
  rw [shape] at h
  exact h

end UInt256Proof
