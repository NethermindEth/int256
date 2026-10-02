import UInt256.Arithmetic.Carry
import CIL.SIMD.VectorLemmas

open CIL CIL.Vector UInt256Model

namespace UInt256Proof.SIMD

def carryBit (x y : W64) : W64 := if x + y < x then 1 else 0
def carryMask (x y : W64) : W64 := mask64 ((x + y).ult x)

theorem subtract_mask (x : W64) (p : Bool) :
    x - mask64 p = x + (if p then 1 else 0) := by
  cases p
  · simp [mask64]
  · change x - BitVec.allOnes 64 = x + 1
    rw [BitVec.sub_eq_add_neg, ← BitVec.neg_one_eq_allOnes, BitVec.neg_neg]
    rfl

theorem carryBit_bound (x y : W64) : (carryBit x y).toNat ≤ 1 := by
  unfold carryBit
  split <;> decide

theorem carry_base (x y : W64) : carry x y 0 = carryBit x y := by
  have h := carry_expression x y 0 (by decide)
  simpa [carryBit] using h.symm

theorem carry_mask_sum (x y incomingX incomingY : W64) :
    x + y - carryMask incomingX incomingY = x + y + carryBit incomingX incomingY := by
  rw [carryMask, subtract_mask]
  simp only [carryBit, BitVec.ult_eq_decide_lt, decide_eq_true_eq]

theorem bit_zero_or_one (c : W64) (h : c.toNat ≤ 1) : c = 0 ∨ c = 1 := by
  have hc : c.toNat = 0 ∨ c.toNat = 1 := by omega
  rcases hc with hc | hc
  · left; exact BitVec.eq_of_toNat_eq (by simpa using hc)
  · right; exact BitVec.eq_of_toNat_eq (by simpa using hc)

/-- A received carry creates an extra outgoing carry exactly when the speculative sum wraps. -/
theorem carry_no_propagation (x y c : W64) (hc : c.toNat ≤ 1)
    (h : c = 1 → x + y + 1 ≠ 0) : carry x y c = carryBit x y := by
  rcases bit_zero_or_one c hc with hc0 | hc1
  · subst c; exact carry_base x y
  · subst c
    have hn : ¬ x + y + 1 < x + y := by
      rw [increment_lt]
      exact h rfl
    have hh := carry_expression x y 1 (by decide)
    simp only [hn, ite_false] at hh
    exact hh.symm.trans (BitVec.add_zero (carryBit x y))

def propagationBit (x y c : W64) : W64 :=
  if c = 1 ∧ x + y + c = 0 then 1 else 0

theorem carry_after_incoming (x y c : W64) (hc : c.toNat ≤ 1) :
    carry x y c = carryBit x y + propagationBit x y c := by
  rcases bit_zero_or_one c hc with hc0 | hc1
  · subst c
    rw [carry_base]
    simp only [propagationBit, show (0 : W64) ≠ 1 by decide, false_and, ite_false]
    exact (BitVec.add_zero _).symm
  · subst c
    have hh := carry_expression x y 1 (by decide)
    simp only [increment_lt] at hh
    simpa only [carryBit, propagationBit, eq_self, true_and] using hh.symm

theorem propagationBit_bound (x y c : W64) : (propagationBit x y c).toNat ≤ 1 := by
  unfold propagationBit
  split <;> decide

/-- A lane that already generated carry cannot also propagate its incoming carry. -/
theorem generated_propagation_disjoint (x y c : W64) (hc : c.toNat ≤ 1)
    (hg : carryBit x y = 1) : propagationBit x y c = 0 := by
  have hxy : x + y < x := by
    unfold carryBit at hg
    split at hg
    · assumption
    · contradiction
  have hn := overflow_disjoint x y c hc hxy
  rcases bit_zero_or_one c hc with hc0 | hc1
  · subst c
    simp only [propagationBit, show (0 : W64) ≠ 1 by decide, false_and, ite_false]
  · subst c
    rw [increment_lt] at hn
    simp only [propagationBit, eq_self, true_and, hn, ite_false]

theorem mask_of_generated (x y : W64) (h : carryBit x y = 1) :
    carryMask x y = BitVec.allOnes 64 := by
  have hxy : x + y < x := by
    unfold carryBit at h
    split at h
    · assumption
    · contradiction
  simp only [carryMask, mask64, BitVec.ult_eq_decide_lt, hxy, decide_true, ite_true]
  rfl

theorem masked_carry_no_propagation (x y previousLeft previousRight : W64)
    (h : mask64 ((x + y - carryMask previousLeft previousRight) == 0) &&&
      carryMask previousLeft previousRight = 0) :
    carryBit previousLeft previousRight = 1 → x + y + 1 ≠ 0 := by
  intro hg hz
  have hm := mask_of_generated previousLeft previousRight hg
  have hr : x + y - carryMask previousLeft previousRight = 0 := by
    rw [carry_mask_sum, hg]
    exact hz
  have impossible : (BitVec.allOnes 64) = (0 : W64) := by
    rw [hr] at h
    have ho : ~~~(0 : W64) = BitVec.allOnes 64 := by decide
    simpa only [hm, BEq.rfl, mask64, ite_true, ho,
      BitVec.and_self] using h
  exact (by decide : (BitVec.allOnes 64) ≠ (0 : W64)) impossible

theorem increment_full (x : W64) : x + 1 = 0 ↔ x = BitVec.allOnes 64 := by
  have hx := x.isLt
  simp only [← BitVec.toNat_inj, BitVec.toNat_add, BitVec.toNat_allOnes]
  change (x.toNat + 1) % 2^64 = 0 ↔ x.toNat = 2^64 - 1
  omega

def fullPropagationBit (sum incoming : W64) : W64 :=
  if sum = BitVec.allOnes 64 ∧ incoming = 1 then 1 else 0

theorem fullPropagationBit_bound (sum incoming : W64) :
    (fullPropagationBit sum incoming).toNat ≤ 1 := by
  unfold fullPropagationBit
  split <;> decide

/-- The second repair hop is sufficient after the first hop reaches a full lane. -/
theorem propagation_two_hops (x y g p : W64)
    (hg : g.toNat ≤ 1) (hp : p.toNat ≤ 1) (hd : g = 1 → p = 0) :
    propagationBit x y (g + p) =
      propagationBit x y g ||| fullPropagationBit (x + y + g) p := by
  rcases bit_zero_or_one g hg with hg0 | hg1
  · subst g
    rcases bit_zero_or_one p hp with hp0 | hp1
    · subst p
      simp [propagationBit, fullPropagationBit]
    · subst p
      have hi : x + y + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 ↔
          x + y = BitVec.ofNat 64 (2^64 - 1) := increment_full (x + y)
      simp [propagationBit, fullPropagationBit]
      simp only [hi]
  · subst g
    rw [hd rfl]
    simp [propagationBit, fullPropagationBit]

def armRepairWords (a b : Limbs) : Limbs :=
  let g0 := carryBit (a 0) (b 0)
  let g1 := carryBit (a 1) (b 1)
  let g2 := carryBit (a 2) (b 2)
  let p1 := propagationBit (a 1) (b 1) g0
  let p2 := propagationBit (a 2) (b 2) g1
  let q2 := fullPropagationBit (a 2 + b 2 + g1) p1
  fun i => if i.val = 0 then a 0 + b 0 else
    if i.val = 1 then a 1 + b 1 + g0 else
    if i.val = 2 then a 2 + b 2 + g1 + p1 else
      a 3 + b 3 + g2 + (p2 ||| q2)

/-- ARM's two high-half repair hops are the same ripple sum, including cross-half cascades. -/
theorem arm_repair_sum (a b : Limbs) : value (armRepairWords a b) = value a + value b := by
  let g0 := carryBit (a 0) (b 0)
  let g1 := carryBit (a 1) (b 1)
  let g2 := carryBit (a 2) (b 2)
  let p1 := propagationBit (a 1) (b 1) g0
  have c1 : carry (a 0) (b 0) 0 = g0 := carry_base _ _
  have c2 : carry (a 1) (b 1) g0 = g1 + p1 :=
    carry_after_incoming _ _ _ (carryBit_bound _ _)
  have hc2 : (g1 + p1).toNat ≤ 1 := by
    rw [← c2]
    exact carry_bound _ _ _ (carryBit_bound _ _)
  have hd : g1 = 1 → p1 = 0 :=
    generated_propagation_disjoint _ _ _ (carryBit_bound _ _)
  have hops := propagation_two_hops (a 2) (b 2) g1 p1
    (carryBit_bound _ _) (propagationBit_bound _ _ _) hd
  have c3 := carry_after_incoming (a 2) (b 2) (g1 + p1) hc2
  rw [hops] at c3
  have hs := four_limb_sum a b
  dsimp only at hs
  rw [c1, c2, c3] at hs
  have hw : armRepairWords a b = (fun i => if i.val = 0 then a 0 + b 0 else
      if i.val = 1 then a 1 + b 1 + g0 else
      if i.val = 2 then a 2 + b 2 + (g1 + p1) else
        a 3 + b 3 + (g2 + (propagationBit (a 2) (b 2) g1 |||
          fullPropagationBit (a 2 + b 2 + g1) p1))) := by
    funext i
    simp only [armRepairWords, g0, g1, g2, p1]
    split <;> try rfl
    split <;> try rfl
    split <;> simp only [BitVec.add_assoc]
  rw [hw]
  exact hs

theorem carry_mask_negative (x y : W64) : carryMask x y = -(carryBit x y) := by
  by_cases h : x + y < x
  · simp only [carryMask, carryBit, mask64, BitVec.ult_eq_decide_lt, h, decide_true, ite_true]
    decide
  · simp [carryMask, carryBit, mask64, BitVec.ult_eq_decide_lt, h]

theorem propagation_mask (x y previousLeft previousRight : W64) :
    mask64 ((x + y - carryMask previousLeft previousRight) == BitVec.ofNat 64 0) &&&
      carryMask previousLeft previousRight =
        -(propagationBit x y (carryBit previousLeft previousRight)) := by
  rw [carry_mask_negative, BitVec.sub_eq_add_neg, BitVec.neg_neg]
  rcases bit_zero_or_one (carryBit previousLeft previousRight) (carryBit_bound _ _)
    with h0 | h1
  · rw [h0]
    simp [propagationBit]
  · rw [h1]
    have ho : -(1 : W64) = BitVec.allOnes 64 := by decide
    rw [ho]
    simp only [BitVec.and_allOnes]
    unfold propagationBit mask64
    by_cases hz : x + y + 1 = 0
    · simp only [hz, ite_true, eq_self, true_and]
      decide
    · have hn : (x + y + 1 == BitVec.ofNat 64 0) = false := by
        simp only [beq_eq_false_iff_ne]
        exact hz
      simp only [hn, hz, ite_false, eq_self, true_and]
      decide

theorem negative_bits_or (p q : W64) (hp : p.toNat ≤ 1) (hq : q.toNat ≤ 1) :
    (-p) ||| (-q) = -(p ||| q) := by
  rcases bit_zero_or_one p hp with h0 | h1 <;>
    rcases bit_zero_or_one q hq with k0 | k1
  all_goals subst p; subst q; decide

theorem full_mask (sum incoming : W64) (hc : incoming.toNat ≤ 1) :
    mask64 (sum == BitVec.allOnes 64) &&& (-incoming) =
      -(fullPropagationBit sum incoming) := by
  rcases bit_zero_or_one incoming hc with h0 | h1
  · subst incoming; simp [fullPropagationBit]
  · subst incoming
    have ho : -(1 : W64) = BitVec.allOnes 64 := by decide
    rw [ho]
    simp only [BitVec.and_allOnes]
    unfold fullPropagationBit mask64
    by_cases h : sum = BitVec.allOnes 64
    · simp only [h, beq_self_eq_true, ite_true, eq_self, and_self]
      decide
    · have hn : (sum == BitVec.allOnes 64) = false := by
        simp only [beq_eq_false_iff_ne]
        exact h
      simp only [h, hn, ite_false, eq_self, and_true]
      decide

def speculative (a b : Limbs) : Limbs := fun i =>
  a i + b i + if i.val = 0 then 0 else
    carryBit (a ⟨i.val - 1, by omega⟩) (b ⟨i.val - 1, by omega⟩)

/-- The four independently corrected lanes are the ripple sum when no received carry propagates. -/
theorem speculative_sum (a b : Limbs)
    (h1 : carryBit (a 0) (b 0) = 1 → a 1 + b 1 + 1 ≠ 0)
    (h2 : carryBit (a 1) (b 1) = 1 → a 2 + b 2 + 1 ≠ 0) :
    value (speculative a b) = value a + value b := by
  have c1 : carry (a 0) (b 0) 0 = carryBit (a 0) (b 0) := carry_base _ _
  have c2 : carry (a 1) (b 1) (carryBit (a 0) (b 0)) = carryBit (a 1) (b 1) :=
    carry_no_propagation _ _ _ (carryBit_bound _ _) h1
  have c3 : carry (a 2) (b 2) (carryBit (a 1) (b 1)) = carryBit (a 2) (b 2) :=
    carry_no_propagation _ _ _ (carryBit_bound _ _) h2
  have hs := four_limb_sum a b
  dsimp only at hs
  rw [c1, c2, c3] at hs
  have hf : speculative a b = (fun i => if i.val = 0 then a 0 + b 0 else
      if i.val = 1 then a 1 + b 1 + carryBit (a 0) (b 0) else
      if i.val = 2 then a 2 + b 2 + carryBit (a 1) (b 1) else
        a 3 + b 3 + carryBit (a 2) (b 2)) := by
    funext i
    rcases i with ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with h | h | h | h
    all_goals subst i; simp [speculative]
  rw [hf]
  exact hs

end UInt256Proof.SIMD
