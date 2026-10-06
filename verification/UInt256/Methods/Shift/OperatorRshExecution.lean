import UInt256.Methods.Shift.ExecutionAutomation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Shift

theorem execute_operator_right_small (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack ((limbs 0 >>> (count.toNat % 64)) ||| ((limbs 1 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 1 >>> (count.toNat % 64)) ||| ((limbs 2 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64)))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  shift_value_case memory, input, limbs, reads with word

theorem execute_operator_right_word_1 (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 1)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack ((limbs 1 >>> (count.toNat % 64)) ||| ((limbs 2 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64))
        0)]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  shift_value_case memory, input, limbs, reads with word

theorem execute_operator_right_word_2 (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 2)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64))
        0
        0)]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  shift_value_case memory, input, limbs, reads with word

theorem execute_operator_right_word_3 (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (word : count.sshiftRight 6 = (BitVec.ofNat 32 3)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack (limbs 3 >>> (count.toNat % 64))
        0
        0
        0)]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  shift_value_case memory, input, limbs, reads with word

theorem execute_operator_right_negative (memory : Memory) (input frame fuel : Nat) (limbs : Limbs)
    (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i)))
    (unsigned : ¬ (count.sshiftRight 6).toNat < 4)
    (signed : (count.sshiftRight 6).toInt < 0)
    (nonzero : count &&& (63 : W32) ≠ (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 (pack ((limbs 0 >>> (count.toNat % 64)) ||| ((limbs 1 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 1 >>> (count.toNat % 64)) ||| ((limbs 2 <<< 1) <<< (63 - count.toNat % 64)))
        ((limbs 2 >>> (count.toNat % 64)) ||| ((limbs 3 <<< 1) <<< (63 - count.toNat % 64)))
        (limbs 3 >>> (count.toNat % 64)))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  change count &&& BitVec.ofNat 32 63 ≠ BitVec.ofNat 32 0 at nonzero
  have signedNormalized : count.toInt >>> 6 < 0 := by simpa only [BitVec.toInt_sshiftRight] using signed
  have signedBranch : ¬ (0 : Int) ≤ count.toInt >>> 6 := by omega
  have unsignedNormalized : ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using unsigned
  shift_value_case memory, input, limbs, reads with unsignedNormalized, signedBranch, nonzero

theorem execute_operator_right_zero (memory : Memory) (input frame fuel : Nat) (count : W32)
    (outside : ¬ (count.sshiftRight 6).toNat < 4)
    (zero : 0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : W32) = (0 : W32)) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory =
        some (final, [.v256 ((0 : BitVec 256))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  shift_zero_value count, outside, zero
end UInt256Proof.Shift
