import UInt256.Methods.Add.SmallCarryBranch
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Safety

open UInt256Model.Safety

def incrementedWords (count : Nat) (words : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 :=
  fun i => if 0 < i.val ∧ i.val ≤ count then words i + 1 else words i

theorem incrementedWords_next (segment : Fin 3) (words : Fin 4 → BitVec 64) :
    (fun i => if i = (⟨segment.val + 1, by omega⟩ : Fin 4)
      then incrementedWords segment.val words i + 1 else incrementedWords segment.val words i) =
      incrementedWords (segment.val + 1) words := by
  obtain ⟨n, bound⟩ := segment
  have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp [incrementedWords]

theorem small_stopped_words (segment : Fin 3) (words : Fin 4 → BitVec 64) (word : BitVec 64)
    (carry : words 0 + word < words 0)
    (previous : ∀ i : Fin 4, 0 < i.val → i.val ≤ segment.val → words i + 1 = 0)
    (stop : words ⟨segment.val + 1, by omega⟩ + 1 ≠ 0) :
    smallCarryOutput segment.val (words 0 + word) (incrementedWords (segment.val + 1) words) =
      UInt256Proof.smallResult words word := by
  have p1 := previous 1
  have p2 := previous 2
  simp only [BitVec.ofNat_eq_ofNat] at p1 p2 stop
  obtain ⟨n, bound⟩ := segment
  have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp at p1 p2 stop
    funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [smallCarryOutput, incrementedWords, UInt256Proof.smallResult, carry, p1, p2, stop]

theorem small_overflow_words (words : Fin 4 → BitVec 64) (word : BitVec 64)
    (carry : words 0 + word < words 0)
    (first : words 1 + 1 = 0) (second : words 2 + 1 = 0) (third : words 3 + 1 = 0) :
    (fun i : Fin 4 => if i.val = 0 then words 0 + word else 0) = UInt256Proof.smallResult words word := by
  simp only [BitVec.ofNat_eq_ofNat] at first second third
  funext ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [UInt256Proof.smallResult, carry, first, second, third]

theorem small_result_value (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference) (word : BitVec 64) :
    UInt256Model.value (UInt256Proof.smallResult (inputLimb memory input) word) =
      inputValue memory input + BitVec.ofNat 256 word.toNat := by
  rw [UInt256Proof.small_result_sum]
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [initial]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

def smallOverflow (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference) (word : BitVec 64) : BitVec 32 :=
  if 2^256 ≤ (inputValue memory input).toNat + word.toNat then 1 else 0

theorem smallOverflow_cases (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference) (word : BitVec 64) :
    smallOverflow memory input word =
      if inputLimb memory input 0 + word < inputLimb memory input 0 ∧
        inputLimb memory input 1 + 1 = 0 ∧ inputLimb memory input 2 + 1 = 0 ∧
        inputLimb memory input 3 + 1 = 0 then 1 else 0 := by
  have overflow := UInt256Proof.Reporting.small_overflow_iff (inputLimb memory input) word
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  have wideBound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
  rw [initial] at overflow
  simp [UInt256Model.value, UInt256Proof.singleLimb, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt wideBound] at overflow
  unfold smallOverflow
  simp only [BitVec.ofNat_eq_ofNat, Nat.reducePow, ← overflow]

#print axioms incrementedWords_next
#print axioms small_stopped_words
#print axioms small_overflow_words
#print axioms small_result_value
#print axioms smallOverflow_cases

end UInt256Proof.Safety
