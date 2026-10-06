import UInt256.Methods.Multiply.BothTwoSafetyFinalColumn
import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ZeroProducts
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def bothTwoResultWords (original : Memory) (left right : Reference) : UInt256Model.Limbs := fun index =>
  let known := bothTwoFinalWords original left right
  if index.val = 0 then localWord known 4 else
  if index.val = 1 then localWord known 8 else
  if index.val = 2 then localWord known 11 else localWord known 12 + localWord known 7

theorem both_two_words_correct (original : Memory) (left right : Reference)
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0)
    (rightUpper : inputLimb original right 2 = 0 ∧ inputLimb original right 3 = 0) :
    UInt256Model.value (bothTwoResultWords original left right) = inputValue original left * inputValue original right := by
  have words : bothTwoResultWords original left right = productLimbs (inputLimb original left) (inputLimb original right) := by
    funext ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases leftUpper with ⟨left2, left3⟩
    rcases rightUpper with ⟨right2, right3⟩
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [bothTwoResultWords, bothTwoFinalWords, bothTwoSecondColumn, bothTwoFirstProducts,
        bothTwoInputs, localWord, widenWords, countWords, rememberWord,
        productLimbs, firstColumn, secondColumn, topWords, column, columnStep,
        left2, left3, right2, right3, countCarry, BitVec.add_assoc]
  rw [words, product_limbs_correct, input_limbs_value, input_limbs_value]

#print axioms both_two_words_correct
end UInt256Proof.Multiply.Safety
