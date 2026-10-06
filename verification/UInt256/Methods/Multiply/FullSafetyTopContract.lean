import UInt256.Methods.Multiply.FullSafetySetup

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def FullTopContract : Prop :=
  ∀
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord (fullInputs original left right) 6 (fullTop original left right)) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 96 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned),
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 18 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned

end UInt256Proof.Multiply.Safety
