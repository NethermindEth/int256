import UInt256.Methods.Shift.ProfileCoverage
import UInt256.Methods.Shift.Entry
import UInt256.Methods.Shift.Outputs
import UInt256.Methods.Shift.Invocation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Shift

theorem execute_left_result (memory : Memory) (input out frame fuel : Nat)
    (limbs : Limbs) (count : W32)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (limbs i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object input, .i32 count, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = writeBytes memory out
        (result .left (value limbs) count).toNat 32 (.byte address) := by
  have lowBound : count.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases negative : count.toInt < 0
  · have signed := (word_count_negative count).mpr negative
    have outside := word_negative_unsigned count signed
    by_cases multiple : count.toNat % 64 = 0
    · obtain ⟨final, execution, bytes⟩ := execute_left_zero memory input out frame fuel count
        outside (Or.inr (mask_zero count multiple))
      refine ⟨final, execution, ?_⟩
      intro address
      simpa only [result, effectiveCount_negative_zero count negative multiple,
        zero_nat] using bytes address
    · obtain ⟨final, execution, bytes⟩ := execute_left_negative memory input out frame fuel limbs count
        reads outside signed (mask_nonzero count multiple)
      refine ⟨final, execution, ?_⟩
      intro address
      rw [bytes, left_store_zero memory out limbs _ lowBound]
      simp only [result, effectiveCount_negative count negative multiple]
  · have nonnegative : 0 ≤ count.toInt := by omega
    by_cases small : count.toNat < 256
    · have quotient : count.toNat / 64 < 4 := by omega
      have decomposition := Nat.mod_add_div count.toNat 64
      by_cases zero : count.toNat / 64 = 0
      · have word := word_count_eq count nonnegative 0 (by decide) zero
        obtain ⟨final, execution, bytes⟩ := execute_left_small memory input out frame fuel limbs count reads word
        refine ⟨final, execution, ?_⟩
        intro address
        rw [bytes, left_store_zero memory out limbs _ lowBound]
        have amount : count.toNat % 64 = count.toNat := by omega
        simp only [amount, result, effectiveCount_nonnegative count nonnegative small]
      · by_cases one : count.toNat / 64 = 1
        · have word := word_count_eq count nonnegative 1 (by decide) one
          obtain ⟨final, execution, bytes⟩ := execute_left_word_1 memory input out frame fuel limbs count reads word
          refine ⟨final, execution, ?_⟩
          intro address
          rw [bytes, left_store_one memory out limbs _ lowBound]
          have amount : 64 + count.toNat % 64 = count.toNat := by omega
          simp only [amount, result, effectiveCount_nonnegative count nonnegative small]
        · by_cases two : count.toNat / 64 = 2
          · have word := word_count_eq count nonnegative 2 (by decide) two
            obtain ⟨final, execution, bytes⟩ := execute_left_word_2 memory input out frame fuel limbs count reads word
            refine ⟨final, execution, ?_⟩
            intro address
            rw [bytes, left_store_two memory out limbs _ lowBound]
            have amount : 128 + count.toNat % 64 = count.toNat := by omega
            simp only [amount, result, effectiveCount_nonnegative count nonnegative small]
          · have three : count.toNat / 64 = 3 := by omega
            have word := word_count_eq count nonnegative 3 (by decide) three
            obtain ⟨final, execution, bytes⟩ := execute_left_word_3 memory input out frame fuel limbs count reads word
            refine ⟨final, execution, ?_⟩
            intro address
            rw [bytes, left_store_three memory out limbs _ lowBound]
            have amount : 192 + count.toNat % 64 = count.toNat := by omega
            simp only [amount, result, effectiveCount_nonnegative count nonnegative small]
    · have largeNat : 256 ≤ count.toNat := by omega
      have largeInt : 256 ≤ count.toInt := by rw [count_nonnegative_cast count nonnegative]; omega
      have large := (word_count_large count).mpr largeInt
      obtain ⟨final, execution, bytes⟩ := execute_left_zero memory input out frame fuel count
        (word_large_unsigned count large) (Or.inl (by omega))
      refine ⟨final, execution, ?_⟩
      intro address
      simpa only [result, effectiveCount_large count nonnegative largeNat,
        zero_nat] using bytes address

theorem lsh_correct (initial : Bytes) (input out : Nat) (count : W32) :
    Contract .left Extracted.program Extracted.entryIndex initial input out count := by
  let memory := initLocals (byteMemory initial) 0 Extracted.entryBody.locals
  have reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) =
      some (.i64 (inputLimbs initial input i)) := by
    intro i
    simp only [memory, read64_initLocals_byte]
    exact read64_initial initial input i
  obtain ⟨final, execution, bytes⟩ := execute_left_result memory input out 0 0
    (inputLimbs initial input) count reads
  refine ⟨executionBound Extracted.program Extracted.entryIndex, final, ?_, ?_⟩
  · apply invoke_plain Extracted.program Extracted.entryIndex Extracted.entryBody
      (by simp only [cil_code]) (by simp only [cil_code]) (by simp only [cil_code])
    simpa only [Nat.zero_add] using execution
  · rw [input_value] at bytes
    intro address
    rw [bytes]
    exact writeBytes_congr memory (byteMemory initial)
      (by intro location; simp [memory, initLocals_bytes]) _ _ _ address

theorem checked_contract : ∀ (initial : Bytes) (input out : Nat) (count : W32),
    Contract .left Extracted.program Extracted.entryIndex initial input out count := lsh_correct

theorem checked_contract_profile (profile : FeatureProfile)
    (agreement : Extracted.program.ProfileAgreement Extracted.profile profile)
    (initial : Bytes) (input out : Nat) (count : W32) :
    Contract .left (reprofile Extracted.program profile) Extracted.entryIndex initial input out count := by
  obtain ⟨fuel, final, execution, bytes⟩ := checked_contract initial input out count
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

theorem lsh_storage_profile_check : storageProgramCheck Extracted.program = true := by rfl

theorem lsh_profile_agreement (profile : FeatureProfile)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    Extracted.program.ProfileAgreement Extracted.profile profile :=
  storage_profile_agreement _ lsh_storage_profile_check _ _ same

theorem checked_contract_storage_profile (profile : FeatureProfile)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (initial : Bytes) (input out : Nat) (count : W32) :
    Contract .left (reprofile Extracted.program profile) Extracted.entryIndex initial input out count :=
  checked_contract_profile profile (lsh_profile_agreement profile same) initial input out count

end UInt256Proof.Shift

#print axioms UInt256Proof.Shift.checked_contract
#print axioms UInt256Proof.Shift.checked_contract_profile




#print axioms UInt256Proof.Shift.checked_contract_storage_profile
