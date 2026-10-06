import UInt256.Safety.OutputValue
import UInt256.Safety.HalfRepresentation

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
