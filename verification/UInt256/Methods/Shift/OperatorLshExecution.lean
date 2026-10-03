import UInt256.Methods.Shift.Storage
import UInt256.Methods.Shift.Count
import UInt256.Methods.Shift.WholeShift
import UInt256.Methods.Shift.Representation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Shift

theorem execute_operator_left_small (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack (limbs 0 <<< (count.toNat % 64)) ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63-count.toNat%64))) ((limbs 2 <<< (count.toNat % 64)) ||| ((limbs 1 >>> 1) >>> (63-count.toNat%64))) ((limbs 3 <<< (count.toNat % 64)) ||| ((limbs 2 >>> 1) >>> (63-count.toNat%64))))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_home_call)
  all_goals simp [*, nat_carry_count_flat]

theorem execute_operator_left_word_1 (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 1)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack 0 (limbs 0 <<< (count.toNat % 64)) ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63-count.toNat%64))) ((limbs 2 <<< (count.toNat % 64)) ||| ((limbs 1 >>> 1) >>> (63-count.toNat%64))))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_home_call)
  all_goals simp [*, nat_carry_count_flat]

theorem execute_operator_left_word_2 (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 2)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack 0 0 (limbs 0 <<< (count.toNat % 64)) ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63-count.toNat%64))))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_home_call)
  all_goals simp [*, nat_carry_count_flat]

theorem execute_operator_left_word_3 (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 3)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack 0 0 0 (limbs 0 <<< (count.toNat % 64)))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_home_call)
  all_goals simp [*]

theorem execute_operator_left_negative (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (unsigned : ¬ (count.sshiftRight 6).toNat < 4)
    (signed : (count.sshiftRight 6).toInt < 0)
    (nonzero : count &&& (63 : W32) ≠ (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack (limbs 0 <<< (count.toNat % 64)) ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63-count.toNat%64))) ((limbs 2 <<< (count.toNat % 64)) ||| ((limbs 1 >>> 1) >>> (63-count.toNat%64))) ((limbs 3 <<< (count.toNat % 64)) ||| ((limbs 2 >>> 1) >>> (63-count.toNat%64))))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  change count &&& BitVec.ofNat 32 63 ≠ BitVec.ofNat 32 0 at nonzero
  have signedNormalized : count.toInt >>> 6 < 0 := by simpa only [BitVec.toInt_sshiftRight] using signed
  have signedBranch : ¬ (0 : Int) ≤ count.toInt >>> 6 := by omega
  have unsignedNormalized : ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using unsigned
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  cil_execute_core h0, h1, h2, h3, unsignedNormalized, signedBranch, nonzero, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_home_call)
  all_goals simp [*, nat_carry_count_flat]

theorem execute_operator_left_zero (memory : Memory) (input frame fuel : Nat) (count : W32)
    (outside : ¬ (count.sshiftRight 6).toNat < 4)
    (zero : 0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : W32) = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 ((0 : BitVec 256))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  have outsideNormalized : ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using outside
  rcases zero with positive | multiple
  · have positiveNormalized : (0 : Int) ≤ count.toInt >>> 6 := by simpa only [BitVec.toInt_sshiftRight] using positive
    cil_execute_core outsideNormalized, positiveNormalized, eval_init_home, aggregate_snapshot_after_write, writeAggregate_caller, evalMemory, write256 with (first | cil_shift_store_home_call)
    all_goals simp only [write_local_read_byte]
  · change count &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 0 at multiple
    by_cases positiveNormalized : (0 : Int) ≤ count.toInt >>> 6
    all_goals cil_execute_core outsideNormalized, multiple, positiveNormalized, eval_init_home, aggregate_snapshot_after_write, writeAggregate_caller, evalMemory, write256 with (first | cil_shift_store_home_call)
    all_goals simp only [write_local_read_byte]
end UInt256Proof.Shift
