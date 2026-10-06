import UInt256.Methods.Add.ARMSmallCarry
import UInt256.Arithmetic.Carry
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Add.Safety
open UInt256Model.Safety

/-- Execution's explicit limb updates equal the independently proved small sum. -/
theorem arm_small_result_words (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    armSmallOutputWords (armSmallResult words word).1 (words 0 + word) =
      UInt256Proof.smallResult words word := by
  by_cases carry : words 0 + word < words 0 <;>
    by_cases first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
  all_goals
    funext ⟨i, bound⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [armSmallOutputWords, armSmallResult, armCarryResult, armIncrementWord,
        UInt256Proof.smallResult, carry, first, second]

theorem arm_small_result_value (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference)
    (word : BitVec 64) :
    UInt256Model.value (armSmallOutputWords (armSmallResult (inputLimb memory input) word).1
      (inputLimb memory input 0 + word)) = inputValue memory input + BitVec.ofNat 256 word.toNat := by
  rw [arm_small_result_words, UInt256Proof.small_result_sum]
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [initial]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- The returned byte bit is exactly overflow of the mathematical 256-bit sum. -/
theorem arm_small_result_flag (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    (armSmallResult words word).2 =
      if 2^256 ≤ (UInt256Model.value words).toNat + word.toNat then 1 else 0 := by
  have overflow := UInt256Proof.Reporting.small_overflow_iff words word
  have wideBound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
  have single : (UInt256Model.value (UInt256Proof.singleLimb word)).toNat = word.toNat := by
    simp [UInt256Model.value, UInt256Proof.singleLimb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound]
  rw [single] at overflow
  simp only [← overflow]
  by_cases carry : words 0 + word < words 0 <;>
    by_cases first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases third : words 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
  all_goals
    simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second, third]

#print axioms arm_small_result_words
#print axioms arm_small_result_value
#print axioms arm_small_result_flag
end UInt256Proof.Add.Safety
