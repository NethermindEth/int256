import UInt256.Methods.Shift.Contract

open CIL

namespace UInt256Proof.Shift

theorem nat_mask_count (count : Nat) : count &&& 63 = count % 64 :=
  Nat.and_two_pow_sub_one_eq_mod count 6

theorem nat_carry_count (count : Nat) :
    ((2^32 - count % 64 + 63) % 2^32) % 64 = 63 - count % 64 := by
  have bound := Nat.mod_lt count (show 0 < 64 by decide)
  omega

theorem nat_carry_count_flat (count : Nat) :
    (2^32 - count % 64 + 63) % 64 = 63 - count % 64 := by
  have bound := Nat.mod_lt count (show 0 < 64 by decide)
  omega

theorem byte_offset_nat (base offset : Nat) : ((base : Int) + offset).toNat = base + offset := by
  omega

theorem mask_count (count : W32) : (count &&& (63 : W32)).toNat = count.toNat % 64 := by
  simp only [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod count.toNat 6

theorem mask_count_bound (count : W32) : (count &&& (63 : W32)).toNat < 64 := by
  rw [mask_count]
  exact Nat.mod_lt _ (by decide)

theorem carry_count (count : W32) :
    ((63 : W32) - (count &&& 63)).toNat = 63 - count.toNat % 64 := by
  have bound := mask_count_bound count
  rw [BitVec.toNat_sub, mask_count]
  change (2^32 - count.toNat % 64 + 63) % 2^32 = 63 - count.toNat % 64
  omega

theorem carry_count_mask (count : W32) :
    ((63 : W32) - (count &&& 63)).toNat % 64 = 63 - count.toNat % 64 := by
  rw [carry_count]
  exact Nat.mod_eq_of_lt (by omega)

theorem word_count_signed (count : W32) : (count.sshiftRight 6).toInt = count.toInt / 64 := by
  simp [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]

theorem word_count_negative (count : W32) :
    (count.sshiftRight 6).toInt < 0 ↔ count.toInt < 0 := by
  rw [word_count_signed]
  omega

theorem word_count_large (count : W32) :
    4 ≤ (count.sshiftRight 6).toInt ↔ 256 ≤ count.toInt := by
  rw [word_count_signed]
  omega

theorem count_nonnegative_cast (count : W32) (nonnegative : 0 ≤ count.toInt) :
    count.toInt = (count.toNat : Int) := by
  have bound := count.isLt
  rw [BitVec.toInt_eq_toNat_cond] at nonnegative ⊢
  split <;> omega

theorem word_count_eq (count : W32) (nonnegative : 0 ≤ count.toInt)
    (word : Nat) (small : word < 4) (selected : count.toNat / 64 = word) :
    count.sshiftRight 6 = BitVec.ofNat 32 word := by
  have wordNat : (BitVec.ofNat 32 word).toNat = word := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  have wordInt : (BitVec.ofNat 32 word).toInt = (word : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, wordNat]
    split <;> omega
  apply BitVec.eq_of_toInt_eq
  rw [word_count_signed, count_nonnegative_cast count nonnegative, wordInt]
  omega

theorem word_negative_unsigned (count : W32) (negative : (count.sshiftRight 6).toInt < 0) :
    ¬ (count.sshiftRight 6).toNat < 4 := by
  have bound := (count.sshiftRight 6).isLt
  rw [BitVec.toInt_eq_toNat_cond] at negative
  split at negative <;> omega

theorem word_large_unsigned (count : W32) (large : 4 ≤ (count.sshiftRight 6).toInt) :
    ¬ (count.sshiftRight 6).toNat < 4 := by
  rw [BitVec.toInt_eq_toNat_cond] at large
  split at large <;> omega

theorem mask_zero (count : W32) (multiple : count.toNat % 64 = 0) :
    count &&& (63 : W32) = (0 : W32) := by
  change count &&& (63 : W32) = BitVec.ofNat 32 0
  apply BitVec.eq_of_toNat_eq
  simpa only [mask_count, BitVec.toNat_ofNat] using multiple

theorem mask_nonzero (count : W32) (nonmultiple : count.toNat % 64 ≠ 0) :
    count &&& (63 : W32) ≠ (0 : W32) := by
  intro zero
  change count &&& (63 : W32) = BitVec.ofNat 32 0 at zero
  have := congrArg BitVec.toNat zero
  simp only [mask_count, BitVec.toNat_ofNat] at this
  exact nonmultiple this

end UInt256Proof.Shift
