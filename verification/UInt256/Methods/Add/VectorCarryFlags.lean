import UInt256.Methods.Add.VectorParentCascadeMath
import UInt256.Methods.Reporting.VectorArithmetic

namespace UInt256Proof.Add.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

theorem vector_cascade_overflow (a b : Limbs) :
    (if (moveMask64 (propagationMask (zip256 (· + ·) (value a) (value b))) +
        2 * moveMask64 (generatedCarry (value a) (value b))) &&& 16 > 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0 := by
  rw [vector_generated_mask, vector_propagated_mask]
  have positive (x : BitVec 32) : x > 0 ↔ x ≠ 0 := UInt256Proof.Reporting.flag32_positive x
  simp only [positive, UInt256Proof.Reporting.cascade_add_flag, UInt256Proof.Reporting.finalCarry_overflow]

theorem vector_full_guard (a b : Limbs)
    (fast : propagationMask (zip256 (· + ·) (value a) (value b)) &&&
      incomingCarry (generatedCarry (value a) (value b)) = BitVec.ofNat 256 0) :
    (¬ (addPropagate a b 1 && addGenerate a b 0) = true) ∧
    (¬ (addPropagate a b 2 && addGenerate a b 1) = true) ∧
    (¬ (addPropagate a b 3 && addGenerate a b 2) = true) := by
  rw [vector_propagation_packed, vector_generated_packed, incomingCarry_packed, pack256_and] at fast
  have zeroAnd (x : BitVec 64) : x &&& (0 : BitVec 64) = BitVec.ofNat 64 0 := BitVec.and_zero
  rw [zeroAnd] at fast
  exact UInt256Proof.Reporting.full_mask_guard _ _ _ _ _ _ fast

theorem vector_fast_overflow (a b : Limbs)
    (fast : propagationMask (zip256 (· + ·) (value a) (value b)) &&&
      incomingCarry (generatedCarry (value a) (value b)) = BitVec.ofNat 256 0) :
    (if moveMask64 (generatedCarry (value a) (value b)) &&& BitVec.ofNat 32 8 > BitVec.ofNat 32 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0 := by
  obtain ⟨no1, no2, no3⟩ := vector_full_guard a b fast
  have flag : (addGenerate a b 3 = true) ↔ 2^256 ≤ (value a).toNat + (value b).toNat := by
    rw [← UInt256Proof.Reporting.finalCarry_overflow, UInt256Proof.Reporting.fast_add_flag a b no1 no2 no3]
    cases h : addGenerate a b 3 <;> simp
  rw [vector_generated_mask]
  simp only [operationMask, UInt256Proof.Reporting.flag32_positive,
    UInt256Proof.Reporting.packed_top_flag, flag]

#print axioms vector_fast_overflow
#print axioms vector_cascade_overflow
#print axioms vector_full_guard
end UInt256Proof.Add.Safety
