import UInt256.Methods.Multiply.LeftTwoSafetyFinal
import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ZeroProducts
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def leftTwoResultWords (original : Memory) (left right : Reference) : UInt256Model.Limbs := fun index =>
  let known := leftTwoFinalWords original left right
  localWord known (if index.val = 0 then 6 else if index.val = 1 then 10 else if index.val = 2 then 13 else 4)

theorem left_two_words_correct (original : Memory) (left right : Reference)
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0) :
    UInt256Model.value (leftTwoResultWords original left right) = inputValue original left * inputValue original right := by
  have words : leftTwoResultWords original left right = productLimbs (inputLimb original left) (inputLimb original right) := by
    funext ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases leftUpper with ⟨left2, left3⟩
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [leftTwoResultWords, leftTwoFinalWords, leftTwoUpperWords, leftTwoUpperProduct, leftTwoMiddleWords,
        leftTwoSecondColumn, leftTwoFirstProducts, leftTwoInputs, leftTwoTop,
        localWord, widenWords, countWords, rememberWord,
        productLimbs, firstColumn, secondColumn, topWords, column, columnStep,
        left2, left3, countCarry, lowProduct, BitVec.add_assoc]
  rw [words, product_limbs_correct, input_limbs_value, input_limbs_value]

#print axioms left_two_words_correct
end UInt256Proof.Multiply.Safety
