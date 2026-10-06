import UInt256.Methods.Shift.Count

namespace UInt256Proof.Shift.Safety

/-- The normal count route agrees with the public full-Int32 specification. -/
theorem shift_bounded_count (count : BitVec 32)
    (small : count.sshiftRight 6 < BitVec.ofNat 32 4) :
    effectiveCount count = some (64 * (count.sshiftRight 6).toNat + count.toNat % 64) := by
  change (count.sshiftRight 6).toNat < 4 at small
  have nonnegative : 0 ≤ count.toInt := by
    by_cases negative : count.toInt < 0
    · exact False.elim (word_negative_unsigned count ((word_count_negative count).mpr negative) small)
    · omega
  have shiftedNonnegative : 0 ≤ (count.sshiftRight 6).toInt := by
    have := word_count_negative count
    omega
  have quotient := word_count_signed count
  rw [count_nonnegative_cast count nonnegative,
    count_nonnegative_cast (count.sshiftRight 6) shiftedNonnegative] at quotient
  have bound : count.toNat < 256 := by omega
  rw [effectiveCount_nonnegative count nonnegative bound]
  congr 1
  omega

theorem shift_selected_count (count whole : BitVec 32)
    (small : whole < BitVec.ofNat 32 4)
    (selected : whole = count.sshiftRight 6 ∨
      (whole = 0 ∧ (count.sshiftRight 6).toInt < 0 ∧ count &&& (63 : BitVec 32) ≠ 0)) :
    effectiveCount count = some (64 * whole.toNat + count.toNat % 64) := by
  rcases selected with rfl | ⟨rfl, negative, nonzero⟩
  · exact shift_bounded_count count small
  · have nonmultiple : count.toNat % 64 ≠ 0 := fun h => nonzero (mask_zero count h)
    simpa using effectiveCount_negative count ((word_count_negative count).mp negative) nonmultiple

/-- Every route to the zero store is specified to return mathematical zero. -/
theorem shift_zero_count (count : BitVec 32)
    (large : ¬ count.sshiftRight 6 < BitVec.ofNat 32 4)
    (selected : 0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : BitVec 32) = 0) :
    effectiveCount count = none := by
  by_cases negative : count.toInt < 0
  · have shiftedNegative := (word_count_negative count).mpr negative
    have masked : count &&& (63 : BitVec 32) = 0 := by rcases selected with h | h <;> omega
    have multiple : count.toNat % 64 = 0 := by
      change count &&& (63 : BitVec 32) = BitVec.ofNat 32 0 at masked
      have h := congrArg BitVec.toNat masked
      simpa only [mask_count, BitVec.toNat_ofNat] using h
    exact effectiveCount_negative_zero count negative multiple
  · have nonnegative : 0 ≤ count.toInt := by omega
    have bound : 256 ≤ count.toNat := by
      by_cases small : count.toNat < 256
      · have wholeSmall : count.toNat / 64 < 4 := by omega
        have equal := word_count_eq count nonnegative _ wholeSmall rfl
        apply False.elim
        apply large
        rw [equal]
        change (BitVec.ofNat 32 (count.toNat / 64)).toNat < 4
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact wholeSmall
      · omega
    exact effectiveCount_large count nonnegative bound

#print axioms shift_selected_count
#print axioms shift_zero_count
end UInt256Proof.Shift.Safety
