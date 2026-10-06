import UInt256.Methods.Multiply.ScalarSafetyLadder
import UInt256.Methods.Multiply.ScalarProduct

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def ladderWords (known : Nat → Option (BitVec 64)) (result : Nat) (low high incoming : BitVec 64) :=
  rememberWord (rememberWord (rememberWord known 5 low) result (low + incoming)) 3 (high + sumHigh low incoming)

def scalarProducts (original : Memory) (input : Reference) (word : BitVec 64) : Nat → Option (BitVec 64) :=
  ladderWords
    (ladderWords (scalarFirstProduct original input word) 6
      (lowProduct word (inputLimb original input 1)) (highProduct word (inputLimb original input 1))
      (highProduct word (inputLimb original input 0))) 7
    (lowProduct word (inputLimb original input 2)) (highProduct word (inputLimb original input 2))
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))

/-- Compose the original-input loads and three widening calls, including both
    carry updates. The untouched high input limb stays on the evaluation stack. -/
theorem scalar_products (contract : WordContract)
    (original entered current : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity scalarBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [input] [output] frame (scalarProducts original input word) →
      ∃ fuel final returned,
        run Extracted.program fuel scalarIndex 66 (scalarArgs input word output) frame
          [.scalar (.i64 (inputLimb original input 3))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 22 (scalarArgs input word output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply scalar_inputs original entered current input output word frame originalCall enteredWF homes state post
  intro prepared preparedState
  apply scalar_first_product contract original entered prepared input output word frame
    originalCall enteredWF homes preparedState post
  intro first firstState
  apply scalar_next_product false contract original entered first input output word (inputLimb original input 1)
    frame _ _ originalCall enteredWF homes firstState (by simp [ladderInput, scalarFirstProduct, scalarInputs, rememberWord]) post
  intro second secondState
  apply scalar_accumulate false original entered second input output word
    (lowProduct word (inputLimb original input 1)) (highProduct word (inputLimb original input 1))
    (highProduct word (inputLimb original input 0)) frame _ _ enteredWF homes secondState
    (by simp [rememberWord]) (by simp [rememberWord, scalarFirstProduct]) post
  intro summed summedState
  apply scalar_next_product true contract original entered summed input output word (inputLimb original input 2)
    frame _ _ originalCall enteredWF homes summedState
    (by simp [ladderInput, ladderResult, scalarFirstProduct, scalarInputs, rememberWord]) post
  intro third thirdState
  apply scalar_accumulate true original entered third input output word
    (lowProduct word (inputLimb original input 2)) (highProduct word (inputLimb original input 2))
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))
    frame _ _ enteredWF homes thirdState (by simp [rememberWord])
    (by simp [rememberWord, scalarCarry]) post
  exact continuation

#print axioms scalar_products
end UInt256Proof.Multiply.Safety
