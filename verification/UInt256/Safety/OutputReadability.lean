import UInt256.Safety.OutputValue
import CIL.Safety.ReadCoverage

namespace UInt256Model.Safety
open CIL.Safety

/-- Four initialized readable limbs cover the entire output. A writable output
    alone would not justify the aggregate load used by a value-returning API. -/
theorem output_readable_of_limbs (memory : Memory) (output : Reference)
    (writable : access memory output 32 1 true = .ok ())
    (limbs : ∀ i : Fin 4, ∃ bytes,
      read memory { output with offset := output.offset + 8 * i.val } 8 1 = .ok bytes) :
    ∃ bytes, read memory output 32 1 = .ok bytes := by
  obtain ⟨allocation, ready⟩ := access_requirements writable
  refine ⟨_, read_of_cover ready ?_⟩
  intro i bound
  let limb : Fin 4 := ⟨i / 8, by omega⟩
  obtain ⟨bytes, loaded⟩ := limbs limb
  exact ⟨8 * limb.val, 8, bytes, by dsimp [limb]; omega,
    by dsimp [limb]; omega, loaded⟩

/-- Decode a checked full-width snapshot using the same caller-byte value as
    the arithmetic postcondition, without presuming initialized storage. -/
theorem output_snapshot_value (memory : Memory) (output : Reference) (bytes : List (BitVec 8))
    (loaded : read memory output 32 1 = .ok bytes) :
    BitVec.ofNat 256 (CIL.Safety.byteNumber bytes) = inputValue memory output := by
  rw [read_result_snapshot loaded,
    byteNumber_snapshot (fun offset => (memory.cells output.allocation offset).bits) output.offset 32]
  rfl

#print axioms output_readable_of_limbs
#print axioms output_snapshot_value
end UInt256Model.Safety
