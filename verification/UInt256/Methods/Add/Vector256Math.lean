import UInt256.Methods.Add.VectorCarryFlags
import UInt256.Methods.Subtract.Vector256Math
import UInt256.RepresentationLemmas

open CIL CIL.Vector UInt256Model UInt256Proof.SIMD UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Vector256

/-- The AVX512VL ternary-logic sign mask is the AVX2 carry comparison mask. -/
theorem ternary_carry_lanes (left right : BitVec 256) :
    map256 (fun x => x.sshiftRight 63)
      (ternaryLogic left right (zip256 (· + ·) left right) (BitVec.ofNat 8 212)) =
      generatedCarry left right := by
  rw [← UInt256Proof.value_decode left, ← UInt256Proof.value_decode right]
  simp only [UInt256Proof.Equality.value_pack, zip256, lane256_0, lane256_1, lane256_2, lane256_3,
    generatedCarry]
  rw [ternary_carry_packed_normal]

theorem align_carry (mask : BitVec 256) :
    alignRight64 mask (BitVec.ofNat 256 0) 3 = incomingCarry mask := by
  rw [UInt256Proof.Subtract.Vector256.align_incoming, ← pack256_lanes mask, incomingCarry_packed,
    UInt256Proof.Subtract.Vector256.incoming_packed]

/-- A zero full guard also clears the two middle propagation bits the Add entry tests. -/
theorem parent_of_full (propagation incoming : BitVec 256)
    (fast : propagation &&& incoming = BitVec.ofNat 256 0) :
    parentPropagationBits propagation incoming = BitVec.ofNat 32 0 := by
  rw [parentPropagationBits, fast]
  decide

theorem fast_sum_value (a b : BitVec 256)
    (fast : parentPropagationBits (propagationMask (zip256 (· + ·) a b)) (incomingCarry (generatedCarry a b)) =
      BitVec.ofNat 32 0) :
    zip256 (· - ·) (zip256 (· + ·) a b) (incomingCarry (generatedCarry a b)) = a + b := by
  have result := vector_fast_sum (decode a) (decode b)
    (by rwa [UInt256Proof.value_decode, UInt256Proof.value_decode])
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

theorem cascade_sum_value (a b : BitVec 256) :
    zip256 (· + ·) (zip256 (· + ·) a b)
      (cascadeVector (cascadeIndex (moveMask64 (generatedCarry a b))
        (moveMask64 (propagationMask (zip256 (· + ·) a b))))) = a + b := by
  have result := vector_cascade_sum (decode a) (decode b)
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

theorem cascade_flag_value (a b : BitVec 256) :
    (if (moveMask64 (propagationMask (zip256 (· + ·) a b)) + 2 * moveMask64 (generatedCarry a b)) &&& 16 > 0
      then (1 : BitVec 32) else 0) = if 2^256 ≤ a.toNat + b.toNat then 1 else 0 := by
  have result := vector_cascade_overflow (decode a) (decode b)
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

theorem fast_flag_value (a b : BitVec 256)
    (fast : propagationMask (zip256 (· + ·) a b) &&& incomingCarry (generatedCarry a b) = BitVec.ofNat 256 0) :
    (if moveMask64 (generatedCarry a b) &&& BitVec.ofNat 32 8 > BitVec.ofNat 32 0 then (1 : BitVec 32) else 0) =
      if 2^256 ≤ a.toNat + b.toNat then 1 else 0 := by
  have result := vector_fast_overflow (decode a) (decode b)
    (by rwa [UInt256Proof.value_decode, UInt256Proof.value_decode])
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

#print axioms ternary_carry_lanes
#print axioms align_carry
#print axioms parent_of_full
#print axioms fast_sum_value
#print axioms cascade_sum_value
#print axioms cascade_flag_value
#print axioms fast_flag_value
end UInt256Proof.Add.Vector256
