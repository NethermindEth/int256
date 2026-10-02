import UInt256.Arithmetic.Borrow
import CIL.SIMD.VectorLemmas

open CIL UInt256Model CIL.Vector

namespace UInt256Proof

def independentBorrow (x y : W64) : W64 := borrow x y 0

def finalBorrow (a b : Limbs) : W64 :=
  borrow (a 3) (b 3) (borrow (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0)))

def borrowMask (x y : W64) : W64 := mask64 (decide (x < y))

theorem borrow_mask_flag (x y : W64) :
    (if BitVec.ofNat 64 0 < borrowMask x y then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) =
      if independentBorrow x y = BitVec.ofNat 64 0 then BitVec.ofNat 32 0 else BitVec.ofNat 32 1 := by
  by_cases h : x < y
  all_goals simp only [borrowMask, mask64, independentBorrow, borrow_initial, h,
    decide_true, decide_false, ↓reduceIte]
  all_goals decide

theorem borrow_mask_subtract (x y result : W64) :
    result + borrowMask x y = result - independentBorrow x y := by
  unfold borrowMask independentBorrow mask64
  rw [borrow_initial]
  by_cases h : x < y
  · have maskneg : (~~~(0 : W64)) = -(1 : W64) := by decide
    simp only [h, decide_true, ↓reduceIte, maskneg, BitVec.sub_eq_add_neg]
  · simp [h]

theorem borrow_mask_subtract_raw (x y result : W64) :
    result + mask64 (decide (x < y)) = result - independentBorrow x y :=
  borrow_mask_subtract x y result

theorem borrow_without_propagation (x y incoming : W64)
    (hc : incoming.toNat ≤ 1) (hp : x = y → incoming = 0) :
    borrow x y incoming = independentBorrow x y := by
  rw [← borrow_flags_or x y incoming hc]
  by_cases he : x = y
  · rw [hp he]
    simp [independentBorrow]
  · simp [he, independentBorrow]

/-- Fast speculation is valid precisely when an incoming borrow does not
    encounter an equal input limb. The condition includes the top limb because
    the implementation also promises its exact underflow flag. -/
def NoBorrowPropagation (a b : Limbs) : Prop :=
  (a 1 = b 1 → independentBorrow (a 0) (b 0) = 0) ∧
  (a 2 = b 2 → independentBorrow (a 1) (b 1) = 0) ∧
  (a 3 = b 3 → independentBorrow (a 2) (b 2) = 0)

def speculativeDifference (a b : Limbs) : Limbs := fun i =>
  if i.val = 0 then a 0 - b 0 else
  if i.val = 1 then a 1 - b 1 - independentBorrow (a 0) (b 0) else
  if i.val = 2 then a 2 - b 2 - independentBorrow (a 1) (b 1) else
    a 3 - b 3 - independentBorrow (a 2) (b 2)

theorem independent_borrow_chain (a b : Limbs) (hp : NoBorrowPropagation a b) :
    borrow (a 1) (b 1) (borrow (a 0) (b 0) 0) = independentBorrow (a 1) (b 1) ∧
    borrow (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0)) =
      independentBorrow (a 2) (b 2) ∧
    borrow (a 3) (b 3)
      (borrow (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0))) =
      independentBorrow (a 3) (b 3) := by
  have h1 := borrow_without_propagation (a 1) (b 1) (independentBorrow (a 0) (b 0))
    (borrow_bound _ _ _) hp.1
  have h2 := borrow_without_propagation (a 2) (b 2) (independentBorrow (a 1) (b 1))
    (borrow_bound _ _ _) hp.2.1
  have h3 := borrow_without_propagation (a 3) (b 3) (independentBorrow (a 2) (b 2))
    (borrow_bound _ _ _) hp.2.2
  change borrow (a 1) (b 1) (borrow (a 0) (b 0) 0) = _ at h1
  exact ⟨h1, by rw [h1]; exact h2, by rw [h1, h2]; exact h3⟩

theorem speculative_difference_words (a b : Limbs) (hp : NoBorrowPropagation a b) :
    speculativeDifference a b = differenceWords a b := by
  obtain ⟨h1, h2, _⟩ := independent_borrow_chain a b hp
  funext i
  simp only [speculativeDifference, differenceWords]
  rw [h2, h1]
  rfl

theorem speculative_difference_value (a b : Limbs) (hp : NoBorrowPropagation a b) :
    value (speculativeDifference a b) = value a - value b := by
  rw [speculative_difference_words a b hp, four_limb_difference]

def zeroDifferenceMask (x y : W64) : W64 := mask64 ((x - y) == BitVec.ofNat 64 0)

theorem masked_borrow_no_propagation (x y previousLeft previousRight : W64)
    (h : zeroDifferenceMask x y &&& borrowMask previousLeft previousRight = 0) :
    x = y → independentBorrow previousLeft previousRight = 0 := by
  intro he
  subst y
  have hm : borrowMask previousLeft previousRight = 0 := by
    have zeroMask : zeroDifferenceMask x x = BitVec.allOnes 64 := by
      simp [zeroDifferenceMask, mask64]
    rw [zeroMask, BitVec.allOnes_and] at h
    exact h
  unfold borrowMask mask64 at hm
  unfold independentBorrow
  rw [borrow_initial]
  by_cases hp : previousLeft < previousRight
  · simp [hp] at hm
  · simp [hp]

/-- Lanes coalesce across the two halves exactly as in the production guard. -/
def propagation128 (a b : Limbs) : V128 :=
  pack128 (zeroDifferenceMask (a 2) (b 2) &&& borrowMask (a 1) (b 1))
    ((zeroDifferenceMask (a 1) (b 1) &&& borrowMask (a 0) (b 0)) |||
     (zeroDifferenceMask (a 3) (b 3) &&& borrowMask (a 2) (b 2)))

theorem propagation128_zero (a b : Limbs) (h : propagation128 a b = 0) :
    NoBorrowPropagation a b := by
  have h0 := congrArg (fun bits => lane64 bits 0) h
  have h1 := congrArg (fun bits => lane64 bits 1) h
  simp only [propagation128, lane128_0, lane128_1] at h0 h1
  change zeroDifferenceMask (a 2) (b 2) &&& borrowMask (a 1) (b 1) = 0 at h0
  change (zeroDifferenceMask (a 1) (b 1) &&& borrowMask (a 0) (b 0)) |||
    (zeroDifferenceMask (a 3) (b 3) &&& borrowMask (a 2) (b 2)) = 0 at h1
  obtain ⟨hlo, hhi⟩ := BitVec.or_eq_zero_iff.mp h1
  exact ⟨masked_borrow_no_propagation _ _ _ _ hlo,
    masked_borrow_no_propagation _ _ _ _ h0, masked_borrow_no_propagation _ _ _ _ hhi⟩

def propagation256 (a b : Limbs) : V256 :=
  pack256 (BitVec.ofNat 64 0)
    (mask64 (a 1 == b 1) &&& borrowMask (a 0) (b 0))
    (mask64 (a 2 == b 2) &&& borrowMask (a 1) (b 1))
    (mask64 (a 3 == b 3) &&& borrowMask (a 2) (b 2))

theorem equality_mask_no_propagation (x y u v : W64)
    (h : mask64 (x == y) &&& borrowMask u v = 0) :
    x = y → independentBorrow u v = 0 := by
  intro he
  subst y
  have hm : borrowMask u v = 0 := by
    simp only [beq_self_eq_true, mask64, ↓reduceIte] at h
    change BitVec.allOnes 64 &&& borrowMask u v = 0 at h
    rw [BitVec.allOnes_and] at h
    exact h
  apply masked_borrow_no_propagation x x u v
  simp [hm]
  rfl

theorem propagation256_zero (a b : Limbs) (h : propagation256 a b = 0) :
    NoBorrowPropagation a b := by
  have h1 := congrArg (fun bits => lane64 bits 1) h
  have h2 := congrArg (fun bits => lane64 bits 2) h
  have h3 := congrArg (fun bits => lane64 bits 3) h
  simp only [propagation256, lane256_1, lane256_2, lane256_3] at h1 h2 h3
  exact ⟨equality_mask_no_propagation _ _ _ _ h1,
    equality_mask_no_propagation _ _ _ _ h2,
    equality_mask_no_propagation _ _ _ _ h3⟩

end UInt256Proof
