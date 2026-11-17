import Std

namespace UInt256Proof.Shift

def pack (a0 a1 a2 a3 : BitVec 64) : BitVec 256 :=
  ((a3 ++ a2) ++ a1) ++ a0

theorem pack_extract_zero (a0 a1 a2 a3 : BitVec 64) :
    (pack a0 a1 a2 a3).extractLsb' 0 64 = a0 := by
  exact BitVec.extractLsb'_append_eq_right

theorem pack_extract_one (a0 a1 a2 a3 : BitVec 64) :
    (pack a0 a1 a2 a3).extractLsb' 64 64 = a1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi, show ¬64 + i < 64 by omega]

theorem pack_extract_two (a0 a1 a2 a3 : BitVec 64) :
    (pack a0 a1 a2 a3).extractLsb' 128 64 = a2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi, show ¬128 + i < 64 by omega,
    show ¬128 + i - 64 < 64 by omega,
    show 128 + i - 64 - 64 = i by omega]

theorem pack_extract_three (a0 a1 a2 a3 : BitVec 64) :
    (pack a0 a1 a2 a3).extractLsb' 192 64 = a3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi, show ¬192 + i < 64 by omega,
    show ¬192 + i - 64 < 64 by omega,
    show ¬192 + i - 64 - 64 < 64 by omega,
    show 192 + i - 64 - 64 - 64 = i by omega]

theorem pack_extracts (value : BitVec 256) :
    pack (value.extractLsb' 0 64) (value.extractLsb' 64 64)
      (value.extractLsb' 128 64) (value.extractLsb' 192 64) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h0 : i < 64
  · simp [h0]
  · by_cases h1 : i < 128
    · simp [h0, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]
    · by_cases h2 : i < 192
      · simp [h0, show ¬i - 64 < 64 by omega,
          show i - 64 - 64 < 64 by omega,
          show 128 + (i - 64 - 64) = i by omega]
      · simp [h0, show ¬i - 64 < 64 by omega,
          show ¬i - 64 - 64 < 64 by omega,
          show i - 64 - 64 - 64 < 64 by omega,
          show 192 + (i - 64 - 64 - 64) = i by omega]

theorem eq_of_words (left right : BitVec 256)
    (h0 : left.extractLsb' 0 64 = right.extractLsb' 0 64)
    (h1 : left.extractLsb' 64 64 = right.extractLsb' 64 64)
    (h2 : left.extractLsb' 128 64 = right.extractLsb' 128 64)
    (h3 : left.extractLsb' 192 64 = right.extractLsb' 192 64) : left = right := by
  rw [← pack_extracts left, ← pack_extracts right, h0, h1, h2, h3]

end UInt256Proof.Shift
