import UInt256.Methods.Shift.WholeShift
import UInt256.Methods.Shift.Arithmetic
import UInt256.Methods.Shift.Representation

open CIL UInt256Model

namespace UInt256Proof.Shift

theorem left_pack_zero (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      (limbs 0 <<< n)
      ((limbs 1 <<< n) ||| ((limbs 0 >>> 1) >>> (63-n)))
      ((limbs 2 <<< n) ||| ((limbs 1 >>> 1) >>> (63-n)))
      ((limbs 3 <<< n) ||| ((limbs 2 >>> 1) >>> (63-n))) =
    (value limbs) <<< (n) := by
  simp only [right_carry _ n bound]
  rw [← left_words_zero _ _ _ _ n bound, pack_value]

theorem left_pack_one (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      0
      (limbs 0 <<< n)
      ((limbs 1 <<< n) ||| ((limbs 0 >>> 1) >>> (63-n)))
      ((limbs 2 <<< n) ||| ((limbs 1 >>> 1) >>> (63-n))) =
    (value limbs) <<< (64+n) := by
  simp only [right_carry _ n bound]
  rw [← left_words_one _ _ _ _ n bound, pack_value]

theorem left_pack_two (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      0
      0
      (limbs 0 <<< n)
      ((limbs 1 <<< n) ||| ((limbs 0 >>> 1) >>> (63-n))) =
    (value limbs) <<< (128+n) := by
  simp only [right_carry _ n bound]
  rw [← left_words_two _ _ _ _ n bound, pack_value]

theorem left_pack_three (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      0
      0
      0
      (limbs 0 <<< n) =
    (value limbs) <<< (192+n) := by
  rw [← left_words_three _ _ _ _ n bound, pack_value]

theorem right_pack_zero (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      ((limbs 0 >>> n) ||| ((limbs 1 <<< 1) <<< (63-n)))
      ((limbs 1 >>> n) ||| ((limbs 2 <<< 1) <<< (63-n)))
      ((limbs 2 >>> n) ||| ((limbs 3 <<< 1) <<< (63-n)))
      (limbs 3 >>> n) =
    (value limbs) >>> (n) := by
  simp only [left_carry _ n bound]
  rw [← right_words_zero _ _ _ _ n bound, pack_value]

theorem right_pack_one (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      ((limbs 1 >>> n) ||| ((limbs 2 <<< 1) <<< (63-n)))
      ((limbs 2 >>> n) ||| ((limbs 3 <<< 1) <<< (63-n)))
      (limbs 3 >>> n)
      0 =
    (value limbs) >>> (64+n) := by
  simp only [left_carry _ n bound]
  rw [← right_words_one _ _ _ _ n bound, pack_value]

theorem right_pack_two (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      ((limbs 2 >>> n) ||| ((limbs 3 <<< 1) <<< (63-n)))
      (limbs 3 >>> n)
      0
      0 =
    (value limbs) >>> (128+n) := by
  simp only [left_carry _ n bound]
  rw [← right_words_two _ _ _ _ n bound, pack_value]

theorem right_pack_three (limbs : Limbs) (n : Nat) (bound : n < 64) :
    pack
      (limbs 3 >>> n)
      0
      0
      0 =
    (value limbs) >>> (192+n) := by
  rw [← right_words_three _ _ _ _ n bound, pack_value]

end UInt256Proof.Shift
