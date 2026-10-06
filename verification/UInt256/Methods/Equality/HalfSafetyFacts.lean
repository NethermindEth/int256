import UInt256.Safety.HalfAccess
import UInt256.Methods.Equality.VectorLemmas

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem input_halves (memory : Memory) (reference : Reference) :
    inputHalf memory reference 1 ++ inputHalf memory reference 0 = inputValue memory reference := by
  simpa [inputHalf, inputValue, UInt256Model.halfValue, UInt256Model.byteValue] using
    initial_append_halves (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

theorem input_halves_equal (memory : Memory) (left right : Reference) :
    (inputHalf memory left 0 = inputHalf memory right 0 ∧
      inputHalf memory left 1 = inputHalf memory right 1) ↔
      inputValue memory left = inputValue memory right := by
  constructor
  · rintro ⟨lo, hi⟩
    rw [← input_halves memory left, ← input_halves memory right, lo, hi]
  · intro equal
    rw [← input_halves memory left, ← input_halves memory right] at equal
    exact ⟨by simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun bits : BitVec 256 => bits.extractLsb' 0 128) equal,
      by simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun bits : BitVec 256 => bits.extractLsb' 128 128) equal⟩

theorem input_half_difference_zero (memory : Memory) (left right : Reference) :
    ((inputHalf memory left 0 ^^^ inputHalf memory right 0) |||
      (inputHalf memory left 1 ^^^ inputHalf memory right 1)) = BitVec.ofNat 128 0 ↔
      inputValue memory left = inputValue memory right := by
  simp only [BitVec.or_eq_zero_iff (w := 128), BitVec.xor_eq_zero_iff (w := 128),
    input_halves_equal]

#print axioms input_halves
#print axioms input_halves_equal
#print axioms input_half_difference_zero

end UInt256Proof.Equality.Safety
