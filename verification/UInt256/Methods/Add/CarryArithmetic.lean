import UInt256.Methods.Add.CarryState
import UInt256.Methods.Add.SafetyResult
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Safety
open CIL.Safety UInt256Model.Safety

def scalarOverflowFlag (carry : BitVec 64) : BitVec 32 :=
  if BitVec.ofNat 64 0 < carry then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

def scalarSumWord (memory : CIL.Safety.Memory) (left right : Reference) (i : Fin 4) : BitVec 64 :=
  inputLimb memory left i + inputLimb memory right i + scalarCarryValue memory left right i.val

def scalarSumValue (memory : CIL.Safety.Memory) (left right : Reference) : BitVec 256 :=
  let w := scalarSumWord memory left right
  BitVec.ofNat 256 ((w 0).toNat + (w 1).toNat * 2^64 + (w 2).toNat * 2^128 + (w 3).toNat * 2^192)

theorem scalar_sum_words (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarSumWord memory left right = UInt256Proof.sumWords (inputLimb memory left) (inputLimb memory right) := by
  funext i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [scalarSumWord, scalarCarryValue, UInt256Proof.sumWords]

/-- Connect the completed words to the independent 256-bit addition contract. -/
theorem scalar_sum_value (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarSumValue memory left right = inputValue memory left + inputValue memory right := by
  change UInt256Model.value (scalarSumWord memory left right) = _
  rw [scalar_sum_words, UInt256Proof.sumWords_sum]
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [leftValue, rightValue]

theorem scalar_flag_overflow (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarOverflowFlag (scalarCarryValue memory left right 4) = addOverflow memory left right := by
  have same : scalarCarryValue memory left right 4 =
      UInt256Proof.Reporting.finalCarry (inputLimb memory left) (inputLimb memory right) := rfl
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  have overflow := UInt256Proof.Reporting.finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  simp only [BitVec.ofNat_eq_ofNat, leftValue, rightValue] at overflow
  simp only [scalarOverflowFlag, same, UInt256Proof.Reporting.word_positive,
    overflow, addOverflow, BitVec.ofNat_eq_ofNat]

#print axioms scalar_sum_words
#print axioms scalar_sum_value
#print axioms scalar_flag_overflow
end UInt256Proof.Safety
