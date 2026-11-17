import UInt256.Arithmetic.CascadeVectors
import UInt256.Arithmetic.SignMasks
import UInt256.Arithmetic.SIMDCarry

open CIL CIL.Vector UInt256Model

namespace UInt256Proof.SIMD

theorem and_all_ones64 (a : W64) : a &&& BitVec.ofNat 64 18446744073709551615 = a :=
  BitVec.and_allOnes

theorem and_zero64 (a : W64) : a &&& BitVec.ofNat 64 0 = BitVec.ofNat 64 0 :=
  BitVec.and_zero

theorem and_incoming (a b c d : W64) :
    pack256 a b c d &&& pack256 (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 18446744073709551615)
      (BitVec.ofNat 64 18446744073709551615) = pack256 (BitVec.ofNat 64 0) b c d := by
  change pack256 a b c d &&& pack256 0 (BitVec.allOnes 64) (BitVec.allOnes 64)
    (BitVec.allOnes 64) = pack256 0 b c d
  rw [pack256_and]
  have hz : a &&& (0 : W64) = (0 : W64) := BitVec.and_zero
  rw [hz, BitVec.and_allOnes, BitVec.and_allOnes, BitVec.and_allOnes]

theorem mask64_and (p q : Bool) : mask64 p &&& mask64 q = mask64 (p && q) := by
  cases p <;> cases q <;> decide

theorem middle_flags_zero : ∀ p1 p2 p3 : Bool,
    packedFlags false p1 p2 p3 &&& BitVec.ofNat 32 6 = BitVec.ofNat 32 0 →
      (¬ p1 = true) ∧ (¬ p2 = true) := by decide

theorem packed_mask_guard (g0 g1 g2 p1 p2 p3 : Bool)
    (h : moveMask64 (pack256 (BitVec.ofNat 64 0)
        (mask64 p1 &&& mask64 g0) (mask64 p2 &&& mask64 g1)
        (mask64 p3 &&& mask64 g2)) &&& BitVec.ofNat 32 6 = BitVec.ofNat 32 0) :
    (¬ (p1 && g0) = true) ∧ (¬ (p2 && g1) = true) := by
  rw [mask64_and, mask64_and, mask64_and] at h
  have hm := moveMask_flags false (p1 && g0) (p2 && g1) (p3 && g2)
  change moveMask64 (pack256 (BitVec.ofNat 64 0) _ _ _) = _ at hm
  rw [hm] at h
  exact middle_flags_zero _ _ _ h

theorem fast_correction (a b : Limbs)
    (h1 : ¬ (addPropagate a b 1 && addGenerate a b 0) = true)
    (h2 : ¬ (addPropagate a b 2 && addGenerate a b 1) = true) :
    pack256 (a 0 + b 0) (a 1 + b 1 - carryMask (a 0) (b 0))
      (a 2 + b 2 - carryMask (a 1) (b 1)) (a 3 + b 3 - carryMask (a 2) (b 2)) =
      packedLimbs (sumWords a b) := by
  have no1 : carryBit (a 0) (b 0) = 1 → a 1 + b 1 + 1 ≠ 0 := by
    intro generated wrapped
    have full := (increment_wrap_iff (a 1 + b 1)).mp wrapped
    have gen : addGenerate a b 0 = true := by
      unfold carryBit at generated
      split at generated
      · simp [addGenerate, BitVec.ult_eq_decide_lt, *]
      · contradiction
    apply h1
    simp [addPropagate, full, gen]
  have no2 : carryBit (a 1) (b 1) = 1 → a 2 + b 2 + 1 ≠ 0 := by
    intro generated wrapped
    have full := (increment_wrap_iff (a 2 + b 2)).mp wrapped
    have gen : addGenerate a b 1 = true := by
      unfold carryBit at generated
      split at generated
      · simp [addGenerate, BitVec.ult_eq_decide_lt, *]
      · contradiction
    apply h2
    simp [addPropagate, full, gen]
  have c1 := carry_base (a 0) (b 0)
  change carry (a 0) (b 0) (BitVec.ofNat 64 0) = carryBit (a 0) (b 0) at c1
  have c2 := carry_no_propagation (a 1) (b 1) _ (carryBit_bound (a 0) (b 0)) no1
  have c3 := carry_no_propagation (a 2) (b 2) _ (carryBit_bound (a 1) (b 1)) no2
  simp [packedLimbs, sumWords, show (3 : Fin 4).val = 3 from rfl,
    carry_mask_sum]
  rw [c1, c2, c3]

end UInt256Proof.SIMD
