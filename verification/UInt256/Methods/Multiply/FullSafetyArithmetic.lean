import UInt256.Methods.Multiply.FullSafetyFinal
import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ZeroProducts
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullResultWords (original : Memory) (left right : Reference) : UInt256Model.Limbs := fun index =>
  let known := fullFinalWords original left right
  localWord known (if index.val = 0 then 8 else if index.val = 1 then 14 else if index.val = 2 then 15 else 6)

theorem full_words_correct (original : Memory) (left right : Reference) :
    UInt256Model.value (fullResultWords original left right) = inputValue original left * inputValue original right := by
  have words : fullResultWords original left right = productLimbs (inputLimb original left) (inputLimb original right) := by
    funext ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [fullResultWords, fullFinalWords, fullUpperWords, fullFirstUpperWords, fullMiddleWords,
        fullSecondColumn, fullFirstProducts, fullPrepared, fullInputs, fullTop,
        localWord, widenWords, countWords, rememberWord,
        productLimbs, firstColumn, secondColumn, topWords, column, columnStep,
        countCarry, lowProduct, BitVec.add_assoc]
  rw [words, product_limbs_correct, input_limbs_value, input_limbs_value]

#print axioms full_words_correct
end UInt256Proof.Multiply.Safety
