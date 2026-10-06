import UInt256.Methods.Subtract.BorrowState
import UInt256.Methods.Subtract.SafetyResult
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

def scalarUnderflowFlag (borrow : BitVec 64) : BitVec 32 :=
  if BitVec.ofNat 64 0 < borrow then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

def scalarDifferenceWord (memory : CIL.Safety.Memory) (left right : Reference) (i : Fin 4) : BitVec 64 :=
  inputLimb memory left i - inputLimb memory right i - scalarBorrowValue memory left right i.val

def scalarDifferenceValue (memory : CIL.Safety.Memory) (left right : Reference) : BitVec 256 :=
  let w := scalarDifferenceWord memory left right
  BitVec.ofNat 256 ((w 0).toNat + (w 1).toNat * 2^64 + (w 2).toNat * 2^128 + (w 3).toNat * 2^192)

structure ScalarResult (original final : CIL.Safety.Memory) (values : List Value)
    (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = scalarDifferenceValue original left right
  flag : values = [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

theorem scalar_difference_words (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarDifferenceWord memory left right = UInt256Proof.differenceWords (inputLimb memory left) (inputLimb memory right) := by
  funext i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [scalarDifferenceWord, scalarBorrowValue, UInt256Proof.differenceWords, CIL.fin_val_three]

/-- Connect the completed words to the independent 256-bit subtraction contract. -/
theorem scalar_difference_value (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarDifferenceValue memory left right = inputValue memory left - inputValue memory right := by
  change UInt256Model.value (scalarDifferenceWord memory left right) = _
  rw [scalar_difference_words, UInt256Proof.four_limb_difference]
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [leftValue, rightValue]

theorem ScalarResult.modular_difference {original final : CIL.Safety.Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    inputValue final output = inputValue original left - inputValue original right :=
  result.value.trans (scalar_difference_value original left right)

#print axioms scalar_difference_words
#print axioms scalar_difference_value
#print axioms ScalarResult.modular_difference
/-- The return flag denotes underflow of the initial mathematical operands. -/
theorem scalar_flag_underflow (memory : Memory) (left right : Reference) :
    scalarUnderflowFlag (scalarBorrowValue memory left right 4) =
      (if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0) := by
  have same : scalarBorrowValue memory left right 4 =
      UInt256Proof.Reporting.finalBorrow (inputLimb memory left) (inputLimb memory right) := rfl
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  have underflow := UInt256Proof.Reporting.finalBorrow_underflow (inputLimb memory left) (inputLimb memory right)
  simp only [BitVec.ofNat_eq_ofNat, leftValue, rightValue] at underflow
  simp only [scalarUnderflowFlag, same, UInt256Proof.Reporting.word_positive,
    underflow, BitVec.ofNat_eq_ofNat]

#print axioms scalar_flag_underflow
end UInt256Proof.Subtract.Safety
