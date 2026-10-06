import UInt256.Methods.Add.Vector128ARMRepairState

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Reporting

/-- The actual fast-return mask encodes overflow when reporting was requested.
    The wrapping-only ARM guard does not justify this conclusion. -/
theorem vector128_snapshot_fast_flag (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (reporting : flag ≠ BitVec.ofNat 32 0)
    (fast : selectedPropagation128 flag (vector128BranchValue memory left right 11)
      (vector128BranchValue memory left right 12) = BitVec.ofNat 128 0) :
    (if lane64 (vector128SnapshotValue memory left right 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [vector128_branch_low, vector128_branch_high] at fast
  have carry := vector128_reporting_fast_carry (inputLimb memory left) (inputLimb memory right)
    flag reporting fast
  rw [vector128_snapshot_high_carry, lane128_1, carry_mask_negative, ← carry]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

/-- The repaired high mask gives overflow of the original caller operands. -/
theorem vector128_snapshot_repaired_flag (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    (if lane64 (armRepairSnapshot (vector128DecisionValues memory left right flag) 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [vector128_repaired_snapshot_carry, repaired_high_flag]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

#print axioms vector128_snapshot_fast_flag
#print axioms vector128_snapshot_repaired_flag
end UInt256Proof.Add.Safety
