import Std

namespace UInt256Proof.Shift

theorem left_shift_nat (value : BitVec 256) (count : Nat) :
    (value <<< count).toNat = (value.toNat * 2^count) % 2^256 := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem right_shift_nat (value : BitVec 256) (count : Nat) :
    (value >>> count).toNat = value.toNat / 2^count := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem right_carry (word : BitVec 64) (count : Nat) (bound : count < 64) :
    (word >>> 1) >>> (63 - count) = word >>> (64 - count) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2
  omega

theorem left_carry (word : BitVec 64) (count : Nat) (bound : count < 64) :
    (word <<< 1) <<< (63 - count) = word <<< (64 - count) := by
  rw [← BitVec.shiftLeft_add]
  congr 1
  omega

theorem right_carry_zero (word : BitVec 64) :
    (word >>> 1) >>> 63 = 0 := by
  rw [right_carry word 0 (by decide)]
  exact BitVec.ushiftRight_eq_zero (by decide)

theorem left_carry_zero (word : BitVec 64) :
    (word <<< 1) <<< 63 = 0 := by
  rw [left_carry word 0 (by decide)]
  exact BitVec.shiftLeft_eq_zero (by decide)

theorem left_pair_high (low high : BitVec 64) (count : Nat) (bound : count < 64) :
    ((high ++ low) <<< count).extractLsb' 64 64 =
      (high <<< count) ||| (low >>> (64 - count)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  by_cases h : i < count
  · simp [h, hi, show 64 + i < 128 by omega, show ¬64 + i < count by omega,
      show 64 - count + i < 64 by omega, show 64 + i - count = 64 - count + i by omega]
  · simp [h, hi, show 64 + i < 128 by omega, show ¬64 + i < count by omega,
      show ¬64 + i - count < 64 by omega,
      BitVec.getLsbD_of_ge low (64 - count + i) (show 64 ≤ 64 - count + i by omega),
      show 64 + i - count - 64 = i - count by omega]

theorem right_pair_low (low high : BitVec 64) (count : Nat) (bound : count < 64) :
    ((high ++ low) >>> count).extractLsb' 0 64 =
      (low >>> count) ||| (high <<< (64 - count)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 64 - count
  · simp [h, hi, show count + i < 64 by omega]
  · simp [h, hi, show ¬count + i < 64 by omega,
      BitVec.getLsbD_of_ge low (count + i) (show 64 ≤ count + i by omega),
      show count + i - 64 = i - (64 - count) by omega]

end UInt256Proof.Shift
