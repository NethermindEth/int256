import UInt256.Arithmetic.CascadeVectors
import UInt256.Methods.Reporting.Arithmetic

open CIL CIL.Vector UInt256Model UInt256Proof UInt256Proof.SIMD
set_option maxRecDepth 8192

namespace UInt256Proof.Reporting

theorem finalCarry_boolean (a b : Limbs) :
    Reporting.finalCarry a b =
      if addGenerate a b 3 || (addPropagate a b 3 &&
          rippleIncoming (addGenerate a b) (addPropagate a b) 3) then 1 else 0 := by
  have h0 := carry_boolean (a 0) (b 0) false
  have h1 := carry_boolean (a 1) (b 1) (addGenerate a b 0)
  have h2 := carry_boolean (a 2) (b 2)
    (addGenerate a b 1 || (addPropagate a b 1 && addGenerate a b 0))
  have h3 := carry_boolean (a 3) (b 3)
    (addGenerate a b 2 || (addPropagate a b 2 &&
      (addGenerate a b 1 || (addPropagate a b 1 && addGenerate a b 0))))
  simp only [Bool.false_eq_true, ite_false, Bool.and_false, Bool.or_false] at h0
  simp [addGenerate, addPropagate] at h0 h1 h2 h3
  have chain2 := (congrArg (carry (a 1) (b 1)) h0).trans h1
  have chain3 := (congrArg (carry (a 2) (b 2)) chain2).trans h2
  have chain4 := (congrArg (carry (a 3) (b 3)) chain3).trans h3
  simpa [Reporting.finalCarry, rippleIncoming, addGenerate, addPropagate,
    show (3 : Fin 4).val = 3 from rfl] using chain4

theorem finalBorrow_boolean (a b : Limbs) :
    Reporting.finalBorrow a b =
      if subtractGenerate a b 3 || (subtractPropagate a b 3 &&
          rippleIncoming (subtractGenerate a b) (subtractPropagate a b) 3) then 1 else 0 := by
  have h0 := borrow_boolean (a 0) (b 0) false
  have h1 := borrow_boolean (a 1) (b 1) (subtractGenerate a b 0)
  have h2 := borrow_boolean (a 2) (b 2)
    (subtractGenerate a b 1 || (subtractPropagate a b 1 && subtractGenerate a b 0))
  have h3 := borrow_boolean (a 3) (b 3)
    (subtractGenerate a b 2 || (subtractPropagate a b 2 &&
      (subtractGenerate a b 1 || (subtractPropagate a b 1 && subtractGenerate a b 0))))
  simp only [Bool.false_eq_true, ite_false, Bool.and_false, Bool.or_false] at h0
  simp [subtractGenerate, subtractPropagate] at h0 h1 h2 h3
  have chain2 := (congrArg (borrow (a 1) (b 1)) h0).trans h1
  have chain3 := (congrArg (borrow (a 2) (b 2)) chain2).trans h2
  have chain4 := (congrArg (borrow (a 3) (b 3)) chain3).trans h3
  simpa [Reporting.finalBorrow, rippleIncoming, subtractGenerate, subtractPropagate,
    show (3 : Fin 4).val = 3 from rfl] using chain4

/-- The AVX cascade's returned bit is the fourth mathematical ripple flag. -/
theorem packed_final_flag : ∀ g0 g1 g2 g3 p0 p1 p2 p3 : Bool,
    (¬ (g0 && p0) = true) → (¬ (g1 && p1) = true) →
    (¬ (g2 && p2) = true) → (¬ (g3 && p3) = true) →
    ((packedFlags p0 p1 p2 p3 + 2 * packedFlags g0 g1 g2 g3) &&& 16 ≠ 0 ↔
      (g3 || (p3 && (g2 || (p2 && (g1 || (p1 && g0)))))) = true) := by
  intro g0 g1 g2 g3 p0 p1 p2 p3
  cases g0 <;> cases g1 <;> cases g2 <;> cases g3 <;>
    cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> decide

theorem cascade_add_flag (a b : Limbs) :
    ((operationMask (addPropagate a b) + 2 * operationMask (addGenerate a b)) &&& 16 ≠ 0) ↔
      Reporting.finalCarry a b ≠ 0 := by
  have equation := packed_final_flag
    (addGenerate a b 0) (addGenerate a b 1) (addGenerate a b 2) (addGenerate a b 3)
    (addPropagate a b 0) (addPropagate a b 1) (addPropagate a b 2) (addPropagate a b 3)
    (add_flags_disjoint a b 0) (add_flags_disjoint a b 1)
    (add_flags_disjoint a b 2) (add_flags_disjoint a b 3)
  rw [finalCarry_boolean]
  change _ ↔ (if addGenerate a b 3 || (addPropagate a b 3 &&
    (addGenerate a b 2 || (addPropagate a b 2 &&
      (addGenerate a b 1 || (addPropagate a b 1 && addGenerate a b 0)))))
    then (1 : W64) else 0) ≠ 0
  cases h : (addGenerate a b 3 || (addPropagate a b 3 &&
    (addGenerate a b 2 || (addPropagate a b 2 &&
      (addGenerate a b 1 || (addPropagate a b 1 && addGenerate a b 0))))))
  all_goals simpa only [operationMask, h, Bool.false_eq_true, ↓reduceIte, Bool.true_eq,
    ne_eq, eq_self, show (1 : W64) = 0 ↔ False from by decide,
    not_false_eq_true, not_true_eq_false] using equation

theorem cascade_subtract_flag (a b : Limbs) :
    ((operationMask (subtractPropagate a b) + 2 * operationMask (subtractGenerate a b)) &&& 16 ≠ 0) ↔
      Reporting.finalBorrow a b ≠ 0 := by
  have equation := packed_final_flag
    (subtractGenerate a b 0) (subtractGenerate a b 1) (subtractGenerate a b 2) (subtractGenerate a b 3)
    (subtractPropagate a b 0) (subtractPropagate a b 1) (subtractPropagate a b 2) (subtractPropagate a b 3)
    (subtract_flags_disjoint a b 0) (subtract_flags_disjoint a b 1)
    (subtract_flags_disjoint a b 2) (subtract_flags_disjoint a b 3)
  rw [finalBorrow_boolean]
  change _ ↔ (if subtractGenerate a b 3 || (subtractPropagate a b 3 &&
    (subtractGenerate a b 2 || (subtractPropagate a b 2 &&
      (subtractGenerate a b 1 || (subtractPropagate a b 1 && subtractGenerate a b 0)))))
    then (1 : W64) else 0) ≠ 0
  cases h : (subtractGenerate a b 3 || (subtractPropagate a b 3 &&
    (subtractGenerate a b 2 || (subtractPropagate a b 2 &&
      (subtractGenerate a b 1 || (subtractPropagate a b 1 && subtractGenerate a b 0))))))
  all_goals simpa only [operationMask, h, Bool.false_eq_true, ↓reduceIte, Bool.true_eq,
    ne_eq, eq_self, show (1 : W64) = 0 ↔ False from by decide,
    not_false_eq_true, not_true_eq_false] using equation

/-- Reporting's full TestZ guard also excludes propagation out of the top lane. -/
theorem full_mask_guard : ∀ g0 g1 g2 p1 p2 p3 : Bool,
    pack256 (BitVec.ofNat 64 0) (mask64 p1 &&& mask64 g0)
      (mask64 p2 &&& mask64 g1) (mask64 p3 &&& mask64 g2) = 0 →
      (¬ (p1 && g0) = true) ∧ (¬ (p2 && g1) = true) ∧ (¬ (p3 && g2) = true) := by
  decide

theorem fast_ripple_flag : ∀ g0 g1 g2 g3 p1 p2 p3 : Bool,
    (¬ (p1 && g0) = true) → (¬ (p2 && g1) = true) → (¬ (p3 && g2) = true) →
      (g3 || (p3 && (g2 || (p2 && (g1 || (p1 && g0)))))) = g3 := by
  decide

theorem fast_add_flag (a b : Limbs)
    (h1 : ¬ (addPropagate a b 1 && addGenerate a b 0) = true)
    (h2 : ¬ (addPropagate a b 2 && addGenerate a b 1) = true)
    (h3 : ¬ (addPropagate a b 3 && addGenerate a b 2) = true) :
    finalCarry a b = if addGenerate a b 3 then 1 else 0 := by
  rw [finalCarry_boolean]
  change (if addGenerate a b 3 || (addPropagate a b 3 &&
    (addGenerate a b 2 || (addPropagate a b 2 &&
      (addGenerate a b 1 || (addPropagate a b 1 && addGenerate a b 0))))) then 1 else 0) = _
  rw [fast_ripple_flag _ _ _ _ _ _ _ h1 h2 h3]

theorem packed_top_flag : ∀ g0 g1 g2 g3 : Bool,
    packedFlags g0 g1 g2 g3 &&& BitVec.ofNat 32 8 ≠ BitVec.ofNat 32 0 ↔ g3 = true := by
  decide

theorem flag32_positive (x : W32) : BitVec.ofNat 32 0 < x ↔ x ≠ BitVec.ofNat 32 0 := by
  simp only [BitVec.lt_def, Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem packed_bextr_cascade : ∀ p0 p1 p2 p3 g0 g1 g2 g3 : Bool,
    ((bextr32 (packedFlags p0 p1 p2 p3 + BitVec.ofNat 32 2 * packedFlags g0 g1 g2 g3)
      4 1).setWidth 8).zeroExtend 32 =
      if (packedFlags p0 p1 p2 p3 + BitVec.ofNat 32 2 * packedFlags g0 g1 g2 g3) &&&
        BitVec.ofNat 32 16 = BitVec.ofNat 32 0 then BitVec.ofNat 32 0 else BitVec.ofNat 32 1 := by
  decide

#print axioms finalCarry_boolean
#print axioms finalBorrow_boolean
#print axioms packed_final_flag
#print axioms cascade_add_flag
#print axioms cascade_subtract_flag

end UInt256Proof.Reporting
