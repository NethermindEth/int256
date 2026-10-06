import UInt256.Methods.Add.Vector128Decision
import UInt256.Methods.Reporting.SIMD128AddArithmetic

namespace UInt256Proof.Add.Safety
open CIL.Vector UInt256Model UInt256Proof.SIMD

/-- The checked lane operations have the same values as the independent
    carry arithmetic, before any carry propagation repair. -/
theorem vector128_low_corrected (a b : Limbs) :
    corrected128 (halfSum (pack128 (a 0) (a 1)) (pack128 (b 0) (b 1)))
      (incoming128Low (halfCarry
        (halfSum (pack128 (a 0) (a 1)) (pack128 (b 0) (b 1)))
        (pack128 (a 0) (a 1)))) = correctedLo a b := by
  simp only [corrected128, halfSum, halfCarry, incoming128Low, zip128,
    lane128_0, lane128_1, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
    BitVec.sub_zero, correctedLo, carryMask]

theorem vector128_high_corrected (a b : Limbs) :
    corrected128 (halfSum (pack128 (a 2) (a 3)) (pack128 (b 2) (b 3)))
      (incoming128High
        (halfCarry (halfSum (pack128 (a 0) (a 1)) (pack128 (b 0) (b 1))) (pack128 (a 0) (a 1)))
        (halfCarry (halfSum (pack128 (a 2) (a 3)) (pack128 (b 2) (b 3))) (pack128 (a 2) (a 3)))) =
      correctedHi a b := by
  simp only [corrected128, halfSum, halfCarry, incoming128High, zip128,
    lane128_0, lane128_1, correctedHi, carryMask]

theorem vector128_low_propagation (a b : Limbs) :
    propagating128 (correctedLo a b) (pack128 (BitVec.ofNat 64 0) (carryMask (a 0) (b 0))) =
      propagationLo a b := by rfl

theorem vector128_high_propagation (a b : Limbs) :
    propagating128 (correctedHi a b) (pack128 (carryMask (a 1) (b 1)) (carryMask (a 2) (b 2))) =
      propagationHi a b := by rfl

/-- A caller requesting overflow cannot take the ARM sum-only guard. -/
theorem vector128_reporting_fast_guard (a b : Limbs) (flag : BitVec 32)
    (reporting : flag ≠ BitVec.ofNat 32 0)
    (fast : selectedPropagation128 flag (propagationLo a b) (propagationHi a b) = BitVec.ofNat 128 0) :
    propagationLo a b ||| propagationHi a b = BitVec.ofNat 128 0 := by
  simpa only [selectedPropagation128, reporting, and_false, ite_false] using fast

theorem vector128_reporting_fast_carry (a b : Limbs) (flag : BitVec 32)
    (reporting : flag ≠ BitVec.ofNat 32 0)
    (fast : selectedPropagation128 flag (propagationLo a b) (propagationHi a b) = BitVec.ofNat 128 0) :
    UInt256Proof.Reporting.finalCarry a b = carryBit (a 3) (b 3) := by
  exact UInt256Proof.Reporting.unpropagated_high_flag a b
    (vector128_reporting_fast_guard a b flag reporting fast)

/-- Either extracted fast guard excludes the propagation needed for the sum.
    Reporting additionally checks the top-lane propagation in its OR guard. -/
theorem vector128_fast_no_propagation (a b : Limbs) (flag : BitVec 32)
    (fast : selectedPropagation128 flag (propagationLo a b) (propagationHi a b) = BitVec.ofNat 128 0) :
    propagationARM a b = BitVec.ofNat 128 0 := by
  by_cases selected : Extracted.profile.advSimd = true ∧ flag = BitVec.ofNat 32 0
  · simp only [selectedPropagation128, selected, and_self, ite_true] at fast
    simpa only [propagationARM, incoming128_arm_high] using fast
  · simp only [selectedPropagation128, selected, ite_false] at fast
    obtain ⟨low, high⟩ := BitVec.or_eq_zero_iff.mp fast
    simp only [propagationARM, low, high]
    decide

/-- With the actual selected fast guard, both corrected halves are the
    independently specified four-limb modular sum. -/
theorem vector128_fast_words (a b : Limbs) (flag : BitVec 32)
    (fast : selectedPropagation128 flag (propagationLo a b) (propagationHi a b) = BitVec.ofNat 128 0) :
    correctedLo a b = pack128 (sumWords a b 0) (sumWords a b 1) ∧
    correctedHi a b = pack128 (sumWords a b 2) (sumWords a b 3) := by
  constructor
  · rw [corrected_lo_words, arm_repair_words]
  · rw [← repaired_of_no_propagation a b (vector128_fast_no_propagation a b flag fast),
      repaired_hi_words, arm_repair_words]

#print axioms vector128_reporting_fast_carry
#print axioms vector128_low_propagation
#print axioms vector128_high_propagation
#print axioms vector128_reporting_fast_guard
#print axioms vector128_low_corrected
#print axioms vector128_high_corrected
#print axioms vector128_fast_no_propagation
#print axioms vector128_fast_words
end UInt256Proof.Add.Safety
