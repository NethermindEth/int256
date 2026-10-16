import UInt256.Safety.HalfAccess
import UInt256.Safety.LimbAccess
import UInt256.VectorRepresentation
import UInt256.Safety.OutputValue
import UInt256.Safety.PrivateInputValues

namespace UInt256Model.Safety
open CIL.Safety UInt256Proof

/-- Decode a half from the same caller bytes used by the scalar limb model. -/
theorem halfValue_two_words (bytes : Bytes) (base : Nat) :
    halfValue bytes base = CIL.Vector.pack128
      (BitVec.ofNat 64 (UInt256Model.byteNumber bytes base 8))
      (BitVec.ofNat 64 (UInt256Model.byteNumber bytes (base + 8) 8)) := by
  have loaded := read128_of_limbs (byteMemory bytes) base
    (BitVec.ofNat 64 (UInt256Model.byteNumber bytes base 8))
    (BitVec.ofNat 64 (UInt256Model.byteNumber bytes (base + 8) 8))
    (by simp [CIL.read64, read_initial]) (by simp [CIL.read64, read_initial])
  rw [read128_initial] at loaded
  exact CIL.Value.v128.inj (Option.some.inj loaded)

theorem input_half_low (memory : CIL.Safety.Memory) (reference : Reference) :
    inputHalf memory reference 0 = CIL.Vector.pack128
      (inputLimb memory reference 0) (inputLimb memory reference 1) := by
  simpa only [inputHalf, inputLimb, halfValue, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero] using
    halfValue_two_words (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

theorem input_half_high (memory : CIL.Safety.Memory) (reference : Reference) :
    inputHalf memory reference 1 = CIL.Vector.pack128
      (inputLimb memory reference 2) (inputLimb memory reference 3) := by
  simpa only [inputHalf, inputLimb, halfValue, Fin.val_one, Fin.val_two,
    show (3 : Fin 4).val = 3 from rfl, Nat.mul_one, Nat.reduceMul, Nat.add_assoc,
    Nat.reduceAdd] using
    halfValue_two_words (fun offset => (memory.cells reference.allocation offset).bits) (reference.offset + 16)

#print axioms halfValue_two_words
#print axioms input_half_low
#print axioms input_half_high
end UInt256Model.Safety

namespace UInt256Model.Safety
open CIL.Safety UInt256Proof

theorem read_half_number {memory : CIL.Safety.Memory} {reference : Reference} {half : BitVec 128}
    (loaded : read memory reference 16 1 = .ok (numberBytes half.toNat 16)) :
    UInt256Model.byteNumber (fun offset => (memory.cells reference.allocation offset).bits)
      reference.offset 16 = half.toNat := by
  have decoded := congrArg CIL.Safety.byteNumber (read_result_snapshot loaded)
  rw [byteNumber_numberBytes,
    byteNumber_snapshot (fun offset => (memory.cells reference.allocation offset).bits) reference.offset 16] at decoded
  have bound : half.toNat < 256^16 := half.isLt
  rw [Nat.mod_eq_of_lt bound] at decoded
  exact decoded.symm

/-- Two successful half reads determine the whole caller-visible value. -/
theorem output_value_of_half_reads (memory : CIL.Safety.Memory) (output : Reference)
    (low high : BitVec 128)
    (lowRead : read memory output 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read memory { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) :
    inputValue memory output = BitVec.ofNat 256 (low.toNat + 2^128 * high.toNat) := by
  have halves := byteNumber_append (fun offset => (memory.cells output.allocation offset).bits) output.offset 16 16
  have lowNumber := read_half_number lowRead
  have highNumber := read_half_number highRead
  change BitVec.ofNat 256 (UInt256Model.byteNumber
    (fun offset => (memory.cells output.allocation offset).bits) output.offset 32) = _
  rw [halves, lowNumber, highNumber]

theorem output_value_of_packed_halves (memory : CIL.Safety.Memory) (output : Reference) (words : Limbs)
    (lowRead : read memory output 16 1 = .ok (numberBytes (CIL.Vector.pack128 (words 0) (words 1)).toNat 16))
    (highRead : read memory { output with offset := output.offset + 16 } 16 1 =
      .ok (numberBytes (CIL.Vector.pack128 (words 2) (words 3)).toNat 16)) :
    inputValue memory output = value words := by
  rw [output_value_of_half_reads memory output _ _ lowRead highRead, pack128_number, pack128_number]
  unfold value
  congr 1
  simp only [Nat.mul_add, ← Nat.mul_assoc]
  omega

#print axioms read_half_number
#print axioms output_value_of_half_reads
#print axioms output_value_of_packed_halves
end UInt256Model.Safety
