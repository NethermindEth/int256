import UInt256.Methods.Add.SIMD256Arithmetic
import UInt256.Methods.Reporting.VectorArithmetic
import UInt256.Arithmetic.SIMDBorrow
import UInt256.Methods.Equality.Lemmas
import UInt256.LookupTable

open CIL CIL.Vector UInt256Model UInt256Proof.SIMD

namespace UInt256Proof.Subtract.Vector256

/-- Lanes where the left limb is below the right one (AVX2 `LessThan`). -/
def borrowLanes (left right : BitVec 256) : BitVec 256 :=
  zip256 (fun x y => mask64 (x.ult y)) left right

/-- Lanes whose limbs are equal (`Vector256.Equals(av, bv)`). -/
def equalLanes (left right : BitVec 256) : BitVec 256 :=
  zip256 (fun x y => mask64 (x == y)) left right

/-- Each lane receives the mask of the lane below it; lane 0 receives none. -/
def borrowIncoming (mask : BitVec 256) : BitVec 256 :=
  pack256 0 (lane64 mask 0) (lane64 mask 1) (lane64 mask 2)

theorem borrow_lanes_packed (a b : Limbs) :
    borrowLanes (value a) (value b) = pack256
      (mask64 (subtractGenerate a b 0)) (mask64 (subtractGenerate a b 1))
      (mask64 (subtractGenerate a b 2)) (mask64 (subtractGenerate a b 3)) := by
  simp only [borrowLanes, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, subtractGenerate]

theorem equal_lanes_packed (a b : Limbs) :
    equalLanes (value a) (value b) = pack256
      (mask64 (subtractPropagate a b 0)) (mask64 (subtractPropagate a b 1))
      (mask64 (subtractPropagate a b 2)) (mask64 (subtractPropagate a b 3)) := by
  simp only [equalLanes, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, subtractPropagate]

/-- The AVX512VL ternary-logic sign mask is the AVX2 comparison mask. -/
theorem ternary_borrow_lanes (left right : BitVec 256) :
    map256 (fun x => x.sshiftRight 63)
      (ternaryLogic left right (zip256 (· - ·) left right) (BitVec.ofNat 8 142)) =
      borrowLanes left right := by
  rw [← value_decode left, ← value_decode right]
  simp only [UInt256Proof.Equality.value_pack, zip256, lane256_0, lane256_1, lane256_2, lane256_3,
    borrowLanes]
  rw [ternary_borrow_packed_normal]

theorem incoming_packed (a b c d : W64) :
    borrowIncoming (pack256 a b c d) = pack256 0 a b c := by
  simp only [borrowIncoming, lane256_0, lane256_1, lane256_2]

theorem align_incoming (mask : BitVec 256) :
    alignRight64 mask (BitVec.ofNat 256 0) 3 = borrowIncoming mask := by
  rw [← pack256_lanes mask]
  exact (avx512_incoming _ _ _ _).trans (incoming_packed _ _ _ _).symm

theorem permute_incoming (mask : BitVec 256) :
    permute4x64 mask (BitVec.ofNat 8 144) &&&
      pack256 (BitVec.ofNat 64 0) (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 18446744073709551615) =
      borrowIncoming mask := by
  rw [← pack256_lanes mask]
  have hp := avx2_permute_incoming (lane64 mask 0) (lane64 mask 1) (lane64 mask 2) (lane64 mask 3)
  change permute4x64 _ (BitVec.ofNat 8 144) = _ at hp
  rw [hp, and_incoming, incoming_packed]
  rfl

theorem generated_mask (a b : Limbs) :
    moveMask64 (borrowLanes (value a) (value b)) = operationMask (subtractGenerate a b) := by
  rw [borrow_lanes_packed, moveMask_flags]
  rfl

theorem propagated_mask (a b : Limbs) :
    moveMask64 (equalLanes (value a) (value b)) = operationMask (subtractPropagate a b) := by
  rw [equal_lanes_packed, moveMask_flags]
  rfl

/-- The fast guard excludes every borrow that reaches an equal limb. -/
theorem fast_guard (a b : Limbs)
    (fast : equalLanes (value a) (value b) &&& borrowIncoming (borrowLanes (value a) (value b)) = 0) :
    (¬ (subtractPropagate a b 1 && subtractGenerate a b 0) = true) ∧
    (¬ (subtractPropagate a b 2 && subtractGenerate a b 1) = true) ∧
    (¬ (subtractPropagate a b 3 && subtractGenerate a b 2) = true) := by
  rw [equal_lanes_packed, borrow_lanes_packed, incoming_packed, pack256_and] at fast
  have zeroAnd (x : BitVec 64) : x &&& (0 : BitVec 64) = BitVec.ofNat 64 0 := BitVec.and_zero
  rw [zeroAnd, mask64_and, mask64_and, mask64_and] at fast
  exact UInt256Proof.Reporting.full_mask_guard _ _ _ _ _ _ (by
    rw [← mask64_and, ← mask64_and, ← mask64_and] at fast
    exact fast)

theorem no_propagation (a b : Limbs)
    (fast : equalLanes (value a) (value b) &&& borrowIncoming (borrowLanes (value a) (value b)) = 0) :
    NoBorrowPropagation a b := by
  obtain ⟨h1, h2, h3⟩ := fast_guard a b fast
  have step (x y u v : W64) (h : ¬ ((x == y) && u.ult v) = true) :
      x = y → independentBorrow u v = 0 := by
    intro equal
    subst y
    simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true] at h
    simp only [independentBorrow, borrow_initial]
    have : ¬ u < v := by simpa [BitVec.ult_eq_decide_lt] using h
    simp [this]
  exact ⟨step _ _ _ _ h1, step _ _ _ _ h2, step _ _ _ _ h3⟩

/-- Speculative difference with incoming masks equals full subtraction when the guard holds. -/
theorem fast_difference (a b : Limbs)
    (fast : equalLanes (value a) (value b) &&& borrowIncoming (borrowLanes (value a) (value b)) = 0) :
    zip256 (· + ·) (zip256 (· - ·) (value a) (value b))
      (borrowIncoming (borrowLanes (value a) (value b))) = value a - value b := by
  rw [← speculative_difference_value a b (no_propagation a b fast), borrow_lanes_packed,
    incoming_packed]
  simp only [UInt256Proof.Equality.value_pack, zip256, lane256_0, lane256_1, lane256_2, lane256_3]
  have shift (x y r : W64) : r + mask64 (x.ult y) = r - independentBorrow x y := by
    rw [BitVec.ult_eq_decide]
    exact borrow_mask_subtract_raw x y r
  simp only [shift, subtractGenerate, speculativeDifference]
  congr 1 <;> simp

theorem fast_flag (a b : Limbs)
    (fast : equalLanes (value a) (value b) &&& borrowIncoming (borrowLanes (value a) (value b)) = 0) :
    (moveMask64 (borrowLanes (value a) (value b)) &&& BitVec.ofNat 32 8 ≠ BitVec.ofNat 32 0) ↔
      (value a).toNat < (value b).toNat := by
  obtain ⟨h1, h2, h3⟩ := fast_guard a b fast
  have total : UInt256Proof.Reporting.finalBorrow a b = if subtractGenerate a b 3 then 1 else 0 := by
    rw [UInt256Proof.Reporting.finalBorrow_boolean]
    change (if subtractGenerate a b 3 || (subtractPropagate a b 3 &&
      (subtractGenerate a b 2 || (subtractPropagate a b 2 &&
        (subtractGenerate a b 1 || (subtractPropagate a b 1 && subtractGenerate a b 0))))) then 1 else 0) = _
    rw [UInt256Proof.Reporting.fast_ripple_flag _ _ _ _ _ _ _ h1 h2 h3]
  rw [generated_mask, operationMask, UInt256Proof.Reporting.packed_top_flag,
    ← UInt256Proof.Reporting.finalBorrow_underflow, total]
  cases subtractGenerate a b 3 <;> decide

/-- The table correction selected by the actual masks yields full subtraction. -/
theorem cascade_difference (a b : Limbs) :
    zip256 (· - ·) (zip256 (· - ·) (value a) (value b))
      (cascadeVector (cascadeIndex (moveMask64 (borrowLanes (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b))))) = value a - value b := by
  rw [generated_mask, propagated_mask]
  have lanes : zip256 (· - ·) (value a) (value b) = packedLimbs (fun i => a i - b i) := by
    simp only [UInt256Proof.Equality.value_pack, zip256, packedLimbs,
      lane256_0, lane256_1, lane256_2, lane256_3]
  rw [lanes, subtract_cascade_vector]
  change pack256 _ _ _ _ = _
  rw [← UInt256Proof.Equality.value_pack, four_limb_difference]

theorem cascade_flag (a b : Limbs) :
    ((moveMask64 (equalLanes (value a) (value b)) +
        2 * moveMask64 (borrowLanes (value a) (value b))) &&& 16 ≠ 0) ↔
      (value a).toNat < (value b).toNat := by
  rw [generated_mask, propagated_mask, UInt256Proof.Reporting.cascade_subtract_flag,
    UInt256Proof.Reporting.finalBorrow_underflow]

/-- The returned slow-path flag: bit 4 of the cascade sum. -/
def slowFlag (bmi1 : Bool) (sum : BitVec 32) : BitVec 32 :=
  if bmi1 then ((CIL.Vector.bextr32 sum 4 1).setWidth 8).zeroExtend 32
  else if 0#32 < sum &&& 16#32 then 1#32 else 0#32

theorem flag_select {P Q : Prop} [Decidable P] [Decidable Q] (equivalent : P ↔ Q) (x y : BitVec 32) :
    (if P then x else y) = if Q then x else y := by
  by_cases q : Q <;> simp [q, equivalent]

theorem fast_flag_value (a b : Limbs)
    (fast : equalLanes (value a) (value b) &&& borrowIncoming (borrowLanes (value a) (value b)) = 0) :
    (if 0#32 < moveMask64 (borrowLanes (value a) (value b)) &&& 8#32 then 1#32 else 0#32) =
      if (value a).toNat < (value b).toNat then 1#32 else 0#32 := by
  have equivalent := fast_flag a b fast
  rw [← UInt256Proof.Reporting.flag32_positive] at equivalent
  exact flag_select equivalent _ _

theorem slow_flag_value (bmi1 : Bool) (a b : Limbs) :
    slowFlag bmi1 (moveMask64 (equalLanes (value a) (value b)) + 2 * moveMask64 (borrowLanes (value a) (value b))) =
      if (value a).toNat < (value b).toNat then 1#32 else 0#32 := by
  have equivalent := cascade_flag a b
  rw [show (2 : BitVec 32) = 2#32 from rfl, show (16 : BitVec 32) = 16#32 from rfl,
    show (0 : BitVec 32) = 0#32 from rfl] at equivalent
  rw [show (2 : BitVec 32) = 2#32 from rfl]
  cases bmi1
  · rw [← UInt256Proof.Reporting.flag32_positive] at equivalent
    simp only [slowFlag, Bool.false_eq_true, ite_false]
    exact flag_select equivalent _ _
  · simp only [slowFlag, ite_true]
    rw [generated_mask, propagated_mask] at equivalent ⊢
    simp only [operationMask] at equivalent ⊢
    rw [UInt256Proof.Reporting.packed_bextr_cascade, ← ite_not]
    exact flag_select equivalent _ _

#print axioms flag_select
#print axioms fast_flag_value
#print axioms slow_flag_value
#print axioms ternary_borrow_lanes
#print axioms align_incoming
#print axioms permute_incoming
#print axioms fast_difference
#print axioms fast_flag
#print axioms cascade_difference
#print axioms cascade_flag
end UInt256Proof.Subtract.Vector256
