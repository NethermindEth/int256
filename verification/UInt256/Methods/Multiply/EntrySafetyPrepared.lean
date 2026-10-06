import UInt256.Methods.Multiply.EntrySafetyMasks

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def multiplyUpperInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (multiplyLowInputs original left right)
    2 (inputUpper original left)) 3 (inputUpper original right)

def multiplyInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (multiplyUpperInputs original left right)
    4 (inputTail original left)) 5 (inputTail original right)

theorem multiply_prepare (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (multiplyInputs original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel multiplyIndex 28 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply multiply_low_inputs original entered current left right output frame originalCall enteredWF homes state post
  intro m0 state0
  apply multiply_upper_mask false original entered m0 left right output frame _ originalCall enteredWF homes state0 post
  intro m1 state1
  apply multiply_upper_mask true original entered m1 left right output frame _ originalCall enteredWF homes state1 post
  intro m2 state2
  apply multiply_tail_mask false original entered m2 left right output frame _ originalCall enteredWF homes state2 (by rfl) post
  intro m3 state3
  apply multiply_tail_mask true original entered m3 left right output frame _ originalCall enteredWF homes state3 (by rfl) post
  exact continuation

#print axioms multiply_prepare
end UInt256Proof.Multiply.Safety
