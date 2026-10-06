import UInt256.Methods.Shift.ExecutionAutomation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Shift

theorem execute_right_small (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        ((limbs 0 >>> (count.toNat % 64)) ||| ((limbs 1 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 1 >>> (count.toNat % 64)) ||| ((limbs 2 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64)) (.byte address) := by
  shift_word_case memory, input, out, limbs, reads with word

theorem execute_right_word_1 (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 1)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        ((limbs 1 >>> (count.toNat % 64)) ||| ((limbs 2 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64))
        0 (.byte address) := by
  shift_word_case memory, input, out, limbs, reads with word

theorem execute_right_word_2 (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 2)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64))
        0
        0 (.byte address) := by
  shift_word_case memory, input, out, limbs, reads with word

theorem execute_right_word_3 (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 3)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        (limbs 3 >>> (count.toNat % 64))
        0
        0
        0 (.byte address) := by
  shift_word_case memory, input, out, limbs, reads with word

theorem execute_right_negative (memory : Memory) (input out frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (unsigned : ¬ (count.sshiftRight 6).toNat < 4)
    (signed : (count.sshiftRight 6).toInt < 0)
    (nonzero : count &&& (63 : W32) ≠ (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        ((limbs 0 >>> (count.toNat % 64)) ||| ((limbs 1 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 1 >>> (count.toNat % 64)) ||| ((limbs 2 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64)) (.byte address) := by
  change count &&& BitVec.ofNat 32 63 ≠ BitVec.ofNat 32 0 at nonzero
  have signedNormalized : count.toInt >>> 6 < 0 := by simpa only [BitVec.toInt_sshiftRight] using signed
  have signedBranch : ¬ (0 : Int) ≤ count.toInt >>> 6 := by omega
  have unsignedNormalized : ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using unsigned
  shift_word_case memory, input, out, limbs, reads with unsignedNormalized, signedBranch, nonzero

theorem execute_right_zero (memory : Memory) (input out frame fuel : Nat) (count : W32)
    (outside : ¬ (count.sshiftRight 6).toNat < 4)
    (zero : 0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : W32) = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = writeBytes memory out 0 32 (.byte address) := by
  shift_zero_output count, outside, zero
end UInt256Proof.Shift



#print axioms UInt256Proof.Shift.execute_right_small
