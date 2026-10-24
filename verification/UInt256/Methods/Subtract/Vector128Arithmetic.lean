import UInt256.Methods.Subtract.Vector128Start
import UInt256.Arithmetic.SIMDBorrow
import UInt256.Safety.HalfValue
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Subtract.Profile
open CIL.Vector UInt256Model UInt256Proof

theorem pack128_and (a b c d : BitVec 64) : pack128 a b &&& pack128 c d = pack128 (a &&& c) (b &&& d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [pack128, BitVec.getLsbD_and, BitVec.getLsbD_append]
  split <;> intros <;> rfl

theorem pack128_or (a b c d : BitVec 64) : pack128 a b ||| pack128 c d = pack128 (a ||| c) (b ||| d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [pack128, BitVec.getLsbD_or, BitVec.getLsbD_append]
  split <;> intros <;> rfl

/-- Saved operand halves in the order the helper loads them. -/
def limbHalves (a b : Limbs) (i : Fin 4) : BitVec 128 :=
  if i.val = 0 then pack128 (a 0) (a 1) else if i.val = 1 then pack128 (a 2) (a 3)
  else if i.val = 2 then pack128 (b 0) (b 1) else pack128 (b 2) (b 3)

theorem snapshot_four (values : Fin 4 → BitVec 128) :
    subtractSnapshot values 4 = zip128 (· - ·) (values 0) (values 2) := rfl
theorem snapshot_five (values : Fin 4 → BitVec 128) :
    subtractSnapshot values 5 = zip128 (· - ·) (values 1) (values 3) := rfl
theorem snapshot_seven (values : Fin 4 → BitVec 128) :
    subtractSnapshot values 7 = subtractMask (values 1) (values 3) := rfl
theorem snapshot_eight (values : Fin 4 → BitVec 128) :
    subtractSnapshot values 8 = incoming128Low (subtractMask (values 0) (values 2)) := rfl
theorem snapshot_nine (values : Fin 4 → BitVec 128) :
    subtractSnapshot values 9 = incoming128High (subtractMask (values 0) (values 2)) (subtractMask (values 1) (values 3)) := rfl

theorem limb_halves_zero (a b : Limbs) : limbHalves a b 0 = pack128 (a 0) (a 1) := rfl
theorem limb_halves_one (a b : Limbs) : limbHalves a b 1 = pack128 (a 2) (a 3) := rfl
theorem limb_halves_two (a b : Limbs) : limbHalves a b 2 = pack128 (b 0) (b 1) := rfl
theorem limb_halves_three (a b : Limbs) : limbHalves a b 3 = pack128 (b 2) (b 3) := rfl

/-- The coalesced test equals the independent lane-propagation predicate. -/
theorem limb_propagation (a b : Limbs) :
    subtractPropagation (limbHalves a b) = propagation128 a b := by
  simp only [subtractPropagation, snapshot_four, snapshot_five, snapshot_eight, snapshot_nine,
    limb_halves_zero, limb_halves_one, limb_halves_two, limb_halves_three, subtractMask,
    incoming128Low, incoming128High, zip128, lane128_0, lane128_1, pack128_and, pack128_or,
    show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, lane128_zero, propagation128,
    zeroDifferenceMask, borrowMask, BitVec.ult_eq_decide_lt]
  congr 1
  simp

/-- With independent incoming borrows the two fast halves are the speculative difference words. -/
theorem limb_fast_low (a b : Limbs) :
    zip128 (· + ·) (subtractSnapshot (limbHalves a b) 4) (subtractSnapshot (limbHalves a b) 8) =
      pack128 (speculativeDifference a b 0) (speculativeDifference a b 1) := by
  simp only [snapshot_four, snapshot_eight, limb_halves_zero, limb_halves_two, subtractMask,
    incoming128Low, zip128, lane128_0, lane128_1, BitVec.ult_eq_decide_lt, borrow_mask_subtract_raw]
  simp [speculativeDifference]

theorem limb_fast_high (a b : Limbs) :
    zip128 (· + ·) (subtractSnapshot (limbHalves a b) 5) (subtractSnapshot (limbHalves a b) 9) =
      pack128 (speculativeDifference a b 2) (speculativeDifference a b 3) := by
  simp only [snapshot_five, snapshot_nine, limb_halves_zero, limb_halves_one, limb_halves_two,
    limb_halves_three, subtractMask, incoming128High, zip128, lane128_0, lane128_1,
    BitVec.ult_eq_decide_lt, borrow_mask_subtract_raw]
  simp [speculativeDifference, show (3 : Fin 4).val = 3 from rfl]

theorem limb_fast_flag (a b : Limbs) :
    lane64 (subtractSnapshot (limbHalves a b) 7) 1 = borrowMask (a 3) (b 3) := by
  simp only [snapshot_seven, limb_halves_one, limb_halves_three, subtractMask, zip128, lane128_1,
    borrowMask, BitVec.ult_eq_decide_lt]

/-- The fast flag is the exact underflow of the four-limb operands. -/
theorem limb_fast_underflow (a b : Limbs) (none : NoBorrowPropagation a b) :
    (if lane64 (subtractSnapshot (limbHalves a b) 7) 1 > BitVec.ofNat 64 0 then (1 : BitVec 32) else 0) =
      if (value a).toNat < (value b).toNat then 1 else 0 := by
  have chain := (independent_borrow_chain a b none).2.2
  have final : Reporting.finalBorrow a b = independentBorrow (a 3) (b 3) := chain
  have underflow := Reporting.finalBorrow_underflow a b
  rw [final] at underflow
  have flag := borrow_mask_flag (a 3) (b 3)
  rw [limb_fast_flag]
  change (if BitVec.ofNat 64 0 < borrowMask (a 3) (b 3) then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) = _
  rw [flag]
  by_cases zero : independentBorrow (a 3) (b 3) = BitVec.ofNat 64 0
  · have notLess : ¬ (value a).toNat < (value b).toNat := by
      intro less
      exact underflow.mpr less (by simpa using zero)
    simp [zero, notLess]
  · have less : (value a).toNat < (value b).toNat := underflow.mp (by simpa using zero)
    simp [zero, less]

#print axioms pack128_and
#print axioms pack128_or
#print axioms limb_propagation
#print axioms limb_fast_low
#print axioms limb_fast_high
#print axioms limb_fast_flag
#print axioms limb_fast_underflow
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof CIL.Safety

def subtractInputValues (memory : Memory) (left right : Reference) : Fin 4 → BitVec 128 :=
  limbHalves (inputLimb memory left) (inputLimb memory right)

theorem subtract_input_values (memory : Memory) (left right : Reference) :
    subtractInputValues memory left right 0 = inputHalf memory left 0 ∧
    subtractInputValues memory left right 1 = inputHalf memory left 1 ∧
    subtractInputValues memory left right 2 = inputHalf memory right 0 ∧
    subtractInputValues memory left right 3 = inputHalf memory right 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (input_half_low memory left).symm
  · exact (input_half_high memory left).symm
  · exact (input_half_low memory right).symm
  · exact (input_half_high memory right).symm

#print axioms subtract_input_values
end UInt256Proof.Subtract.Profile
