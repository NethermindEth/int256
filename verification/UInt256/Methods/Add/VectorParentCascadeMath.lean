import UInt256.Methods.Add.VectorParentFastMath

namespace UInt256Proof.Add.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

theorem vector_generated_mask (a b : Limbs) :
    moveMask64 (generatedCarry (value a) (value b)) = operationMask (addGenerate a b) := by
  rw [vector_generated_packed, moveMask_flags]
  rfl

theorem vector_propagated_mask (a b : Limbs) :
    moveMask64 (propagationMask (zip256 (· + ·) (value a) (value b))) =
      operationMask (addPropagate a b) := by
  rw [vector_propagation_packed, moveMask_flags]
  rfl

/-- The table correction selected by the actual masks yields full-width addition
    of the original operands, including every cross-limb carry cascade. -/
theorem vector_cascade_sum (a b : Limbs) :
    zip256 (· + ·) (zip256 (· + ·) (value a) (value b))
      (cascadeVector (cascadeIndex (moveMask64 (generatedCarry (value a) (value b)))
        (moveMask64 (propagationMask (zip256 (· + ·) (value a) (value b)))))) =
      value a + value b := by
  rw [vector_generated_mask, vector_propagated_mask]
  have lanes : zip256 (· + ·) (value a) (value b) = packedLimbs (fun i => a i + b i) := by
    simp only [UInt256Proof.Equality.value_pack, zip256, packedLimbs,
      lane256_0, lane256_1, lane256_2, lane256_3]
  rw [lanes, add_cascade_vector]
  change pack256 _ _ _ _ = _
  rw [← UInt256Proof.Equality.value_pack, UInt256Proof.sumWords_sum]

#print axioms vector_generated_mask
#print axioms vector_propagated_mask
#print axioms vector_cascade_sum
end UInt256Proof.Add.Safety
