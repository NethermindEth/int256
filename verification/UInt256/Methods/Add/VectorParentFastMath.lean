import UInt256.Methods.Add.VectorSafetyPropagation
import UInt256.Methods.Add.SIMD256Arithmetic
import UInt256.Methods.Equality.Lemmas

namespace UInt256Proof.Add.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

def parentPropagationBits (propagation incoming : BitVec 256) : BitVec 32 :=
  CIL.Vector.moveMask64 (propagation &&& incoming) &&& BitVec.ofNat 32 6

theorem vector_generated_packed (a b : Limbs) :
    generatedCarry (value a) (value b) = pack256
      (mask64 (addGenerate a b 0)) (mask64 (addGenerate a b 1))
      (mask64 (addGenerate a b 2)) (mask64 (addGenerate a b 3)) := by
  simp only [generatedCarry, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, addGenerate]

theorem vector_propagation_packed (a b : Limbs) :
    propagationMask (zip256 (· + ·) (value a) (value b)) = pack256
      (mask64 (addPropagate a b 0)) (mask64 (addPropagate a b 1))
      (mask64 (addPropagate a b 2)) (mask64 (addPropagate a b 3)) := by
  have ones : ~~~(BitVec.ofNat 256 0) = pack256
      (BitVec.allOnes 64) (BitVec.allOnes 64)
      (BitVec.allOnes 64) (BitVec.allOnes 64) := by decide
  simp only [propagationMask, ones, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, addPropagate]

/-- The extracted fast-branch guard suffices for the speculative output to equal
    addition of the initial operands modulo 2^256. -/
theorem vector_fast_sum (a b : Limbs)
    (fast : parentPropagationBits
      (propagationMask (zip256 (· + ·) (value a) (value b)))
      (incomingCarry (generatedCarry (value a) (value b))) = BitVec.ofNat 32 0) :
    zip256 (· - ·) (zip256 (· + ·) (value a) (value b))
      (incomingCarry (generatedCarry (value a) (value b))) = value a + value b := by
  rw [parentPropagationBits, vector_propagation_packed, vector_generated_packed,
    incomingCarry_packed, pack256_and] at fast
  have zeroAnd (x : BitVec 64) : x &&& (0 : BitVec 64) = BitVec.ofNat 64 0 := BitVec.and_zero
  rw [zeroAnd] at fast
  obtain ⟨no1, no2⟩ := packed_mask_guard _ _ _ _ _ _ fast
  rw [vector_generated_packed, incomingCarry_packed]
  simp only [UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3]
  have subZero (x : BitVec 64) : x - (0 : BitVec 64) = x := BitVec.sub_zero x
  rw [subZero]
  have corrected := fast_correction a b no1 no2
  simpa only [carryMask, addGenerate, packedLimbs,
    ← UInt256Proof.Equality.value_pack, UInt256Proof.sumWords_sum] using corrected

#print axioms vector_generated_packed
#print axioms vector_propagation_packed
#print axioms vector_fast_sum
end UInt256Proof.Add.Safety
