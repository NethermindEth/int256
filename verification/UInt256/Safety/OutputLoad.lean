import CIL.Safety.ReadCoverage
import UInt256.Safety.OutputValue

namespace UInt256Model.Safety

open CIL.Safety

theorem output_snapshot_of_limb_reads (memory : Memory) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (writable : access memory output 32 1 true = .ok ())
    (r0 : read memory output 8 1 = .ok (numberBytes w0.toNat 8))
    (r1 : read memory { output with offset := output.offset + 8 } 8 1 = .ok (numberBytes w1.toNat 8))
    (r2 : read memory { output with offset := output.offset + 16 } 8 1 = .ok (numberBytes w2.toNat 8))
    (r3 : read memory { output with offset := output.offset + 24 } 8 1 = .ok (numberBytes w3.toNat 8)) :
    read memory output 32 1 =
      .ok ((List.range 32).map fun i => (memory.cells output.allocation (output.offset + i)).bits) := by
  obtain ⟨allocation, ready⟩ := access_requirements writable
  apply read_of_cover ready
  intro i bound
  by_cases h0 : i < 8
  · exact ⟨0, 8, _, by omega, by omega, by simpa using r0⟩
  by_cases h1 : i < 16
  · exact ⟨8, 8, _, by omega, by omega, r1⟩
  by_cases h2 : i < 24
  · exact ⟨16, 8, _, by omega, by omega, r2⟩
  · exact ⟨24, 8, _, by omega, by omega, r3⟩

theorem output_load_of_limb_reads (memory : Memory) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (writable : access memory output 32 1 true = .ok ())
    (r0 : read memory output 8 1 = .ok (numberBytes w0.toNat 8))
    (r1 : read memory { output with offset := output.offset + 8 } 8 1 = .ok (numberBytes w1.toNat 8))
    (r2 : read memory { output with offset := output.offset + 16 } 8 1 = .ok (numberBytes w2.toNat 8))
    (r3 : read memory { output with offset := output.offset + 24 } 8 1 = .ok (numberBytes w3.toNat 8)) :
    loadValue memory (.address output) 32 = .ok (.v256 (BitVec.ofNat 256
      (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192))) := by
  have loaded := output_snapshot_of_limb_reads memory output w0 w1 w2 w3 writable r0 r1 r2 r3
  have value := output_value_of_limb_reads memory output w0 w1 w2 w3 r0 r1 r2 r3
  simp only [loadValue, dereference, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [byteNumber_snapshot (fun offset => (memory.cells output.allocation offset).bits) output.offset 32]
  change Except.ok (CIL.Value.v256 (inputValue memory output)) = _
  rw [value]

#print axioms output_snapshot_of_limb_reads
#print axioms output_load_of_limb_reads

end UInt256Model.Safety
