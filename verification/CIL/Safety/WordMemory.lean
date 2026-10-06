import CIL.Safety.ByteEncoding
import CIL.Safety.WriteEffects
import CIL.Safety.Frames

namespace CIL.Safety

theorem decode_word64 (word : BitVec 64) :
    BitVec.ofNat 64 (byteNumber (numberBytes word.toNat 8)) = word := by
  rw [byteNumber_numberBytes]
  have bound : word.toNat < 256^8 := word.isLt
  rw [Nat.mod_eq_of_lt bound]
  simp

theorem load_word64_of_read {memory : Memory} {reference : Reference} {word : BitVec 64}
    (loaded : read memory reference 8 1 = .ok (numberBytes word.toNat 8)) :
    loadValue memory (.address reference) 8 = .ok (.i64 word) := by
  simp only [loadValue, dereference, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, decode_word64]

theorem load_local_word64_of_read {memory : Memory} {reference : Reference} {word : BitVec 64}
    (loaded : read memory reference 8 1 = .ok (numberBytes word.toNat 8)) :
    loadLocal memory (.bytes .word64 reference) = .ok (.scalar (.i64 word)) := by
  simp only [loadLocal, localWidth, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, decode_word64]

/-- Numeric local storage requires write access but no prior initialization. -/
theorem store_local_word64 {memory : Memory} {reference : Reference} (word : BitVec 64)
    (ready : access memory reference 8 1 true = .ok ()) :
    ∃ result,
      write memory reference (numberBytes word.toNat 8) 1 = .ok result ∧
      storeLocal memory (.bytes .word64 reference) (.scalar (.i64 word)) =
        .ok (.bytes .word64 reference, result) ∧
      read result reference 8 1 = .ok (numberBytes word.toNat 8) ∧
      loadLocal result (.bytes .word64 reference) = .ok (.scalar (.i64 word)) := by
  have length : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨result, written⟩ := write_succeeds (bytes := numberBytes word.toNat 8)
    (by simpa only [length] using ready)
  have readback := write_readback _ _ _ _ _ written
  rw [length] at readback
  refine ⟨result, written, ?_, readback, load_local_word64_of_read readback⟩
  simp only [storeLocal, localNumber, localWidth, written, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms decode_word64
#print axioms load_word64_of_read
#print axioms load_local_word64_of_read
#print axioms store_local_word64

end CIL.Safety
