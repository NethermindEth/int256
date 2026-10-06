import UInt256.Methods.Multiply.LeftTwoSafetyColumns

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def leftTwoMiddleWords (original : Memory) (left right : Reference) :=
  let known := leftTwoSecondColumn original left right
  let reset := rememberWord (rememberWord known 13 (localWord known 9)) 9 0
  countWords (countWords reset 13 7 9 13) 13 11 9 13

theorem left_two_middle_column
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity leftTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (leftTwoSecondColumn original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (leftTwoMiddleWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel leftTwoIndex 66 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 51 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  let known := leftTwoSecondColumn original left right
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (localWord known 9) (by rfl))
  obtain ⟨copied, copiedStep, copiedState⟩ := state.store enteredWF homes 13 (by rfl) (localWord known 9)
    52 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := leftTwoBody)
  apply run_next_exists post found (by rfl) copiedStep
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, resetStep, state0⟩ := copiedState.store enteredWF homes 9 (by rfl) 0
    55 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := leftTwoBody)
  apply run_next_exists post found (by rfl) resetStep
  let k0 := rememberWord (rememberWord known 13 (localWord known 9)) 9 0
  apply run_local_word_call state0 originalCall enteredWF homes 13 7 9 13
    (localWord k0 13) (localWord k0 7) (countCarry (localWord k0 13) (localWord k0 7) 0)
    (localWord k0 13 + localWord k0 7) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state0.snapshots state0.call.1.1 9 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 13 7 9 13
  apply run_local_word_call state1 originalCall enteredWF homes 13 11 9 13
    (localWord k1 13) (localWord k1 11) (countCarry (localWord k1 13) (localWord k1 11) (localWord k1 9))
    (localWord k1 13 + localWord k1 11) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 9 _ _ (localWord k1 9) (by rfl)) post
  exact continuation

#print axioms left_two_middle_column
end UInt256Proof.Multiply.Safety
