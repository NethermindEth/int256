import Std

namespace UInt256Proof.Shift

theorem right_add (value : BitVec width) (first second : Nat) :
    value >>> (first + second) = (value >>> first) >>> second := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, Nat.pow_add]

theorem extract_beyond (value : BitVec width) (start : Nat) (bound : width ≤ start) :
    value.extractLsb' start length = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  simp [hi, BitVec.getLsbD_of_ge value (start + i) (by omega)]

theorem left_extract_move (value : BitVec width) (start count : Nat)
    (startBound : count ≤ start) (endBound : start + 64 ≤ width) :
    (value <<< count).extractLsb' start 64 = value.extractLsb' (start - count) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
  simp [hi, show start + i < width by omega, show ¬start + i < count by omega,
    show start + i - count = start - count + i by omega]

theorem left_extract_zero (value : BitVec width) (start count : Nat)
    (countBound : start + 64 ≤ count) :
    (value <<< count).extractLsb' start 64 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
  simp [show start + i < count by omega]

theorem right_extract_move (value : BitVec width) (start count : Nat) :
    (value >>> count).extractLsb' start 64 = value.extractLsb' (start + count) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  congr 2
  omega

theorem left_extract_low (value : BitVec width) (count : Nat) (widthBound : 64 ≤ width) :
    (value <<< count).extractLsb' 0 64 = value.extractLsb' 0 64 <<< count := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, Nat.zero_add]
  by_cases h : i < count
  · simp [h, hi]
  · simp [h, hi, show i < width by omega, show i - count < 64 by omega]

theorem left_extract_word (value : BitVec width) (start count : Nat)
    (startBound : 64 ≤ start) (endBound : start + 64 ≤ width) (countBound : count < 64) :
    (value <<< count).extractLsb' start 64 =
      (value.extractLsb' start 64 <<< count) |||
        (value.extractLsb' (start - 64) 64 >>> (64 - count)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
  by_cases h : i < count
  · simp [h, hi, show start + i < width by omega,
      show ¬start + i < count by omega,
      show 64 - count + i < 64 by omega,
      show start - 64 + (64 - count + i) = start + i - count by omega]
  · simp [h, hi, show start + i < width by omega,
      show ¬start + i < count by omega,
      show ¬64 - count + i < 64 by omega,
      show start + (i - count) = start + i - count by omega,
      show i - count < 64 by omega]

theorem right_extract_word (value : BitVec width) (start count : Nat)
    (countBound : count < 64) :
    (value >>> count).extractLsb' start 64 =
      (value.extractLsb' start 64 >>> count) |||
        (value.extractLsb' (start + 64) 64 <<< (64 - count)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
  by_cases h : i < 64 - count
  · simp [h, hi, show count + i < 64 by omega,
      show count + (start + i) = start + (count + i) by omega]
  · simp [h, hi, show ¬count + i < 64 by omega,
      show i - (64 - count) < 64 by omega,
      show start + 64 + (i - (64 - count)) = count + (start + i) by omega]


end UInt256Proof.Shift
