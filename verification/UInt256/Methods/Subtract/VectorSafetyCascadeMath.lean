import UInt256.Methods.Subtract.VectorSafetyReturn
import UInt256.Methods.Reporting.VectorArithmetic

namespace UInt256Proof.Subtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- The two actual vector masks encode the independent limb borrow predicates. -/
theorem vector_generated_mask (a b : Limbs) :
    moveMask64 (generatedBorrow (value a) (value b)) = operationMask (subtractGenerate a b) := by
  simp only [generatedBorrow, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, moveMask_flags,
    operationMask, subtractGenerate]

theorem vector_propagated_mask (a b : Limbs) :
    moveMask64 (equalLanes (value a) (value b)) = operationMask (subtractPropagate a b) := by
  simp only [equalLanes, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, moveMask_flags,
    operationMask, subtractPropagate]

/-- The correction vector produces full-width modular subtraction, independently
    of the extracted instruction sequence. -/
theorem vector_cascade_difference (a b : Limbs) :
    zip256 (· - ·) (zip256 (· - ·) (value a) (value b))
      (cascadeVector (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b))))) = value a - value b := by
  rw [vector_generated_mask, vector_propagated_mask]
  have lanes : zip256 (· - ·) (value a) (value b) = packedLimbs (fun i => a i - b i) := by
    simp only [UInt256Proof.Equality.value_pack, zip256, packedLimbs,
      lane256_0, lane256_1, lane256_2, lane256_3]
  rw [lanes, subtract_cascade_vector]
  change pack256 _ _ _ _ = _
  rw [← UInt256Proof.Equality.value_pack, UInt256Proof.four_limb_difference]

/-- The scalar cascade bit is precisely unsigned underflow of the initial values. -/
theorem vector_cascade_underflow (a b : Limbs) :
    (if (moveMask64 (equalLanes (value a) (value b)) +
        2 * moveMask64 (generatedBorrow (value a) (value b))) &&& 16 > 0
      then (1 : BitVec 32) else 0) =
      if (value a).toNat < (value b).toNat then 1 else 0 := by
  rw [vector_generated_mask, vector_propagated_mask]
  have positive (x : BitVec 32) : x > 0 ↔ x ≠ 0 := by
    exact UInt256Proof.Reporting.flag32_positive x
  simp only [positive, UInt256Proof.Reporting.cascade_subtract_flag,
    UInt256Proof.Reporting.finalBorrow_underflow]

#print axioms vector_generated_mask
#print axioms vector_propagated_mask
#print axioms vector_cascade_difference
#print axioms vector_cascade_underflow
end UInt256Proof.Subtract.Safety
