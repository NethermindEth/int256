import CIL.Safety.ByteEncoding
import UInt256.Safety.OutputAccess
import UInt256.RepresentationLemmas

namespace UInt256Model.Safety

open CIL.Safety

theorem read_limb_number {memory : CIL.Safety.Memory} {reference : Reference} {word : BitVec 64}
    (loaded : read memory reference 8 1 = .ok (numberBytes word.toNat 8)) :
    UInt256Model.byteNumber (fun offset => (memory.cells reference.allocation offset).bits)
      reference.offset 8 = word.toNat := by
  have decoded := congrArg CIL.Safety.byteNumber (read_result_snapshot loaded)
  rw [byteNumber_numberBytes, byteNumber_snapshot (fun offset => (memory.cells reference.allocation offset).bits) reference.offset 8] at decoded
  have bound : word.toNat < 256^8 := word.isLt
  rw [Nat.mod_eq_of_lt bound] at decoded
  exact decoded.symm

/-- The final shared bytes represent the independent four-word mathematical value. -/
theorem output_value_of_limb_reads (memory : CIL.Safety.Memory) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (r0 : read memory output 8 1 = .ok (numberBytes w0.toNat 8))
    (r1 : read memory { output with offset := output.offset + 8 } 8 1 = .ok (numberBytes w1.toNat 8))
    (r2 : read memory { output with offset := output.offset + 16 } 8 1 = .ok (numberBytes w2.toNat 8))
    (r3 : read memory { output with offset := output.offset + 24 } 8 1 = .ok (numberBytes w3.toNat 8)) :
    inputValue memory output = BitVec.ofNat 256
      (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) := by
  let bytes : Bytes := fun offset => (memory.cells output.allocation offset).bits
  have h0 := UInt256Proof.byteNumber_append bytes output.offset 8 24
  have h1 := UInt256Proof.byteNumber_append bytes (output.offset + 8) 8 16
  have h2 := UInt256Proof.byteNumber_append bytes (output.offset + 16) 8 8
  have n0 := read_limb_number (memory := memory) (reference := output) (word := w0) r0
  have n1 := read_limb_number (memory := memory) (reference := { output with offset := output.offset + 8 }) (word := w1) r1
  have n2 := read_limb_number (memory := memory) (reference := { output with offset := output.offset + 16 }) (word := w2) r2
  have n3 := read_limb_number (memory := memory) (reference := { output with offset := output.offset + 24 }) (word := w3) r3
  change UInt256Model.byteNumber bytes output.offset 8 = w0.toNat at n0
  change UInt256Model.byteNumber bytes (output.offset + 8) 8 = w1.toNat at n1
  change UInt256Model.byteNumber bytes (output.offset + 16) 8 = w2.toNat at n2
  change UInt256Model.byteNumber bytes (output.offset + 24) 8 = w3.toNat at n3
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2
  change BitVec.ofNat 256 (UInt256Model.byteNumber bytes output.offset 32) = _
  apply congrArg (BitVec.ofNat 256)
  rw [h0, h1, h2, n0, n1, n2, n3]
  simp only [Nat.mul_add, ← Nat.mul_assoc]
  omega

#print axioms read_limb_number
#print axioms output_value_of_limb_reads

end UInt256Model.Safety
