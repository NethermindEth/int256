import UInt256.Methods.Shift.Storage
import UInt256.Methods.Shift.Count
import UInt256.Methods.Shift.WholeShift
import UInt256.Methods.Shift.Representation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Shift

theorem execute_left_small (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        (limbs 0 <<< (count.toNat % 64))
        ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63 - count.toNat % 64)))
        ((limbs 2 <<< (count.toNat % 64)) ||| ((limbs 1 >>> 1) >>> (63 - count.toNat % 64)))
        ((limbs 3 <<< (count.toNat % 64)) ||| ((limbs 2 >>> 1) >>> (63 - count.toNat % 64))) (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  have h8 : (0 : Int) ≤ (out : Int) + 8 := by omega
  have h16 : (0 : Int) ≤ (out : Int) + 16 := by omega
  have h24 : (0 : Int) ≤ (out : Int) + 24 := by omega
  have ha8 : ((out : Int) + 8).toNat = out + 8 := by omega
  have ha16 : ((out : Int) + 16).toNat = out + 16 := by omega
  have ha24 : ((out : Int) + 24).toNat = out + 24 := by omega
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, h8, h16, h24, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_call | cil_store_call)
  all_goals intro address
  all_goals simp [*, store4, nat_carry_count_flat]

theorem execute_left_word_1 (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 1)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        0
        (limbs 0 <<< (count.toNat % 64))
        ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63 - count.toNat % 64)))
        ((limbs 2 <<< (count.toNat % 64)) ||| ((limbs 1 >>> 1) >>> (63 - count.toNat % 64))) (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  have h8 : (0 : Int) ≤ (out : Int) + 8 := by omega
  have h16 : (0 : Int) ≤ (out : Int) + 16 := by omega
  have h24 : (0 : Int) ≤ (out : Int) + 24 := by omega
  have ha8 : ((out : Int) + 8).toNat = out + 8 := by omega
  have ha16 : ((out : Int) + 16).toNat = out + 16 := by omega
  have ha24 : ((out : Int) + 24).toNat = out + 24 := by omega
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, h8, h16, h24, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_call | cil_store_call)
  all_goals intro address
  all_goals simp [*, store4, nat_carry_count_flat]

theorem execute_left_word_2 (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 2)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        0
        0
        (limbs 0 <<< (count.toNat % 64))
        ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63 - count.toNat % 64))) (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  have h8 : (0 : Int) ≤ (out : Int) + 8 := by omega
  have h16 : (0 : Int) ≤ (out : Int) + 16 := by omega
  have h24 : (0 : Int) ≤ (out : Int) + 24 := by omega
  have ha8 : ((out : Int) + 8).toNat = out + 8 := by omega
  have ha16 : ((out : Int) + 16).toNat = out + 16 := by omega
  have ha24 : ((out : Int) + 24).toNat = out + 24 := by omega
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, h8, h16, h24, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_call | cil_store_call)
  all_goals intro address
  all_goals simp [*, store4, nat_carry_count_flat]

theorem execute_left_word_3 (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 3)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        0
        0
        0
        (limbs 0 <<< (count.toNat % 64)) (.byte address) := by
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  have h8 : (0 : Int) ≤ (out : Int) + 8 := by omega
  have h16 : (0 : Int) ≤ (out : Int) + 16 := by omega
  have h24 : (0 : Int) ≤ (out : Int) + 24 := by omega
  have ha8 : ((out : Int) + 8).toNat = out + 8 := by omega
  have ha16 : ((out : Int) + 16).toNat = out + 16 := by omega
  have ha24 : ((out : Int) + 24).toNat = out + 24 := by omega
  cil_execute_core h0, h1, h2, h3, word, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, h8, h16, h24, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_call | cil_store_call)
  all_goals intro address
  all_goals simp [*, store4]

theorem execute_left_negative (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (unsigned : ¬ (count.sshiftRight 6).toNat < 4)
    (signed : (count.sshiftRight 6).toInt < 0)
    (nonzero : count &&& (63 : W32) ≠ (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        (limbs 0 <<< (count.toNat % 64))
        ((limbs 1 <<< (count.toNat % 64)) ||| ((limbs 0 >>> 1) >>> (63 - count.toNat % 64)))
        ((limbs 2 <<< (count.toNat % 64)) ||| ((limbs 1 >>> 1) >>> (63 - count.toNat % 64)))
        ((limbs 3 <<< (count.toNat % 64)) ||| ((limbs 2 >>> 1) >>> (63 - count.toNat % 64))) (.byte address) := by
  change count &&& BitVec.ofNat 32 63 ≠ BitVec.ofNat 32 0 at nonzero
  have signedNormalized : count.toInt >>> 6 < 0 := by simpa only [BitVec.toInt_sshiftRight] using signed
  have signedBranch : ¬ (0 : Int) ≤ count.toInt >>> 6 := by omega
  have unsignedNormalized : ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using unsigned
  obtain ⟨h0, h1, h2, h3⟩ := limb_reads memory input limbs reads
  have h8 : (0 : Int) ≤ (out : Int) + 8 := by omega
  have h16 : (0 : Int) ≤ (out : Int) + 16 := by omega
  have h24 : (0 : Int) ≤ (out : Int) + 24 := by omega
  have ha8 : ((out : Int) + 8).toNat = out + 8 := by omega
  have ha16 : ((out : Int) + 16).toNat = out + 16 := by omega
  have ha24 : ((out : Int) + 24).toNat = out + 24 := by omega
  cil_execute_core h0, h1, h2, h3, unsignedNormalized, signedBranch, nonzero, mask_count, carry_count_mask,
    nat_mask_count, nat_carry_count, h8, h16, h24, evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
      (first | cil_shift_store_call | cil_store_call)
  all_goals intro address
  all_goals simp [*, store4, nat_carry_count_flat]

theorem execute_left_zero (memory : Memory) (input out frame fuel : Nat) (count : W32)
    (outside : ¬ (count.sshiftRight 6).toNat < 4)
    (zero : 0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : W32) = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = writeBytes memory out 0 32 (.byte address) := by
  have outsideNormalized : ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using outside
  rcases zero with positive | multiple
  · have positiveNormalized : (0 : Int) ≤ count.toInt >>> 6 := by simpa only [BitVec.toInt_sshiftRight] using positive
    cil_execute_core outsideNormalized, positiveNormalized, evalMemory, write256 with (first | cil_shift_store_call | cil_store_call)
    all_goals intro address
    all_goals simp only [writeBytes_write_local, write_local_read_byte]
  · change count &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 0 at multiple
    by_cases positiveNormalized : (0 : Int) ≤ count.toInt >>> 6
    all_goals cil_execute_core outsideNormalized, multiple, positiveNormalized, evalMemory, write256 with (first | cil_shift_store_call | cil_store_call)
    all_goals intro address
    all_goals simp only [writeBytes_write_local, write_local_read_byte]
end UInt256Proof.Shift



#print axioms UInt256Proof.Shift.execute_left_small
