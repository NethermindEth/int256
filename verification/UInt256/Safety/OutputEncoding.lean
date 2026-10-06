import UInt256.Safety.OutputReadability
import CIL.Safety.ByteRoundTrip

namespace UInt256Model.Safety
open CIL.Safety

theorem output_encoded_read (memory : Memory) (output : Reference) (value : BitVec 256)
    (readable : ∃ bytes, read memory output 32 1 = .ok bytes)
    (meaning : inputValue memory output = value) :
    read memory output 32 1 = .ok (numberBytes value.toNat 32) := by
  obtain ⟨bytes, loaded⟩ := readable
  have length : bytes.length = 32 := by rw [read_result_snapshot loaded]; simp
  have decoded := (output_snapshot_value memory output bytes loaded).trans meaning
  have bound : CIL.Safety.byteNumber bytes < 2^256 := by
    have bound := byteNumber_lt bytes
    rw [length] at bound
    exact bound
  have number := congrArg BitVec.toNat decoded
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at number
  rw [← number, ← length, numberBytes_byteNumber]
  simpa only [length] using loaded

#print axioms output_encoded_read
end UInt256Model.Safety
