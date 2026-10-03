import UInt256.Methods.Shift.ProfileCoverage
import UInt256.Methods.Shift.OperatorRshExecution
import UInt256.Methods.Shift.ValueOutputs
import UInt256.Methods.Shift.OperatorContract
import UInt256.Methods.Shift.Invocation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Shift

theorem execute_operator_right_result (memory : Memory) (input frame fuel : Nat)
    (limbs : Limbs) (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count] frame [] memory = some (final, [.v256 (result .right (value limbs) count)]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  have lowBound : count.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases negative : count.toInt < 0
  · have signed := (word_count_negative count).mpr negative
    have outside := word_negative_unsigned count signed
    by_cases multiple : count.toNat % 64 = 0
    · obtain ⟨final, execution, bytes⟩ := execute_operator_right_zero memory input frame fuel count
        outside (Or.inr (mask_zero count multiple))
      refine ⟨final, ?_, bytes⟩
      simpa only [result, effectiveCount_negative_zero count negative multiple] using execution
    · obtain ⟨final, execution, bytes⟩ := execute_operator_right_negative memory input frame fuel limbs count
        reads outside signed (mask_nonzero count multiple)
      refine ⟨final, ?_, bytes⟩
      rw [right_pack_zero limbs _ lowBound] at execution
      simpa only [result, effectiveCount_negative count negative multiple] using execution
  · have nonnegative : 0 ≤ count.toInt := by omega
    by_cases small : count.toNat < 256
    · have quotient : count.toNat / 64 < 4 := by omega
      have decomposition := Nat.mod_add_div count.toNat 64
      by_cases zero : count.toNat / 64 = 0
      · have word := word_count_eq count nonnegative 0 (by decide) zero
        obtain ⟨final, execution, bytes⟩ := execute_operator_right_small memory input frame fuel limbs count reads word
        refine ⟨final, ?_, bytes⟩
        rw [right_pack_zero limbs _ lowBound] at execution
        have amount : count.toNat % 64 = count.toNat := by omega
        simpa only [amount, result, effectiveCount_nonnegative count nonnegative small] using execution
      · by_cases one : count.toNat / 64 = 1
        · have word := word_count_eq count nonnegative 1 (by decide) one
          obtain ⟨final, execution, bytes⟩ := execute_operator_right_word_1 memory input frame fuel limbs count reads word
          refine ⟨final, ?_, bytes⟩
          rw [right_pack_one limbs _ lowBound] at execution
          have amount : 64 + count.toNat % 64 = count.toNat := by omega
          simpa only [amount, result, effectiveCount_nonnegative count nonnegative small] using execution
        · by_cases two : count.toNat / 64 = 2
          · have word := word_count_eq count nonnegative 2 (by decide) two
            obtain ⟨final, execution, bytes⟩ := execute_operator_right_word_2 memory input frame fuel limbs count reads word
            refine ⟨final, ?_, bytes⟩
            rw [right_pack_two limbs _ lowBound] at execution
            have amount : 128 + count.toNat % 64 = count.toNat := by omega
            simpa only [amount, result, effectiveCount_nonnegative count nonnegative small] using execution
          · have three : count.toNat / 64 = 3 := by omega
            have word := word_count_eq count nonnegative 3 (by decide) three
            obtain ⟨final, execution, bytes⟩ := execute_operator_right_word_3 memory input frame fuel limbs count reads word
            refine ⟨final, ?_, bytes⟩
            rw [right_pack_three limbs _ lowBound] at execution
            have amount : 192 + count.toNat % 64 = count.toNat := by omega
            simpa only [amount, result, effectiveCount_nonnegative count nonnegative small] using execution
    · have largeNat : 256 ≤ count.toNat := by omega
      have largeInt : 256 ≤ count.toInt := by rw [count_nonnegative_cast count nonnegative]; omega
      have large := (word_count_large count).mpr largeInt
      obtain ⟨final, execution, bytes⟩ := execute_operator_right_zero memory input frame fuel count
        (word_large_unsigned count large) (Or.inl (by omega))
      refine ⟨final, ?_, bytes⟩
      simpa only [result, effectiveCount_large count nonnegative largeNat] using execution


theorem operator_rsh_correct (initial : Bytes) (input : Nat) (count : W32) :
    OperatorContract .right Extracted.program Extracted.entryIndex initial input count := by
  let memory := initFrame (byteMemory initial) 0 Extracted.entryBody [.object input, .i32 count]
  have caller : ∀ address, memory (.byte address) = byteMemory initial (.byte address) := by
    intro address
    simp [memory, initFrame, cil_code, clearHome_caller, writeAggregate_caller, initLocals_bytes]
  have reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) =
      some (.i64 (inputLimbs initial input i)) := by
    intro i
    rw [read64_congr memory (byteMemory initial) caller]
    exact read64_initial initial input i
  obtain ⟨final, execution, bytes⟩ := execute_operator_right_result memory input 0 0
    (inputLimbs initial input) count reads
  rw [input_value] at execution
  refine ⟨executionBound Extracted.program Extracted.entryIndex, final, ?_, ?_⟩
  · apply invoke_frame Extracted.program Extracted.entryIndex Extracted.entryBody
      (by simp only [cil_code])
    simpa only [Nat.zero_add] using execution
  · intro address
    exact (bytes address).trans (caller address)

theorem operator_rsh_checked_contract : ∀ (initial : Bytes) (input : Nat) (count : W32),
    OperatorContract .right Extracted.program Extracted.entryIndex initial input count := operator_rsh_correct

theorem operator_rsh_storage_profile_check : storageProgramCheck Extracted.program = true := by rfl

theorem operator_rsh_checked_contract_storage_profile (profile : FeatureProfile)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (initial : Bytes) (input : Nat) (count : W32) :
    OperatorContract .right (reprofile Extracted.program profile) Extracted.entryIndex initial input count := by
  obtain ⟨fuel, final, execution, bytes⟩ := operator_rsh_checked_contract initial input count
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile
    (storage_profile_agreement _ operator_rsh_storage_profile_check _ _ same)]
  exact execution

end UInt256Proof.Shift

#print axioms UInt256Proof.Shift.operator_rsh_checked_contract
#print axioms UInt256Proof.Shift.operator_rsh_checked_contract_storage_profile
