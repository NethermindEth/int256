import UInt256.Methods.Multiply.FullSafetyColumns

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullMiddleWords (original : Memory) (left right : Reference) :=
  let known := fullSecondColumn original left right
  let reset := rememberWord (rememberWord known 15 (localWord known 13)) 13 0
  countWords (countWords reset 15 9 13 15) 15 11 13 15

theorem full_middle_column
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullSecondColumn original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullMiddleWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 139 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 124 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let known := fullSecondColumn original left right
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (localWord known 13) (localWord_known _ _ (by rfl)))
  obtain ⟨copied, copiedStep, copiedState⟩ := state.store enteredWF homes 15 (by rfl) (localWord known 13)
    125 (productArgs left right output) [] (body := fullBody)
  apply run_next_exists post found (by rfl) copiedStep
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, resetStep, state0⟩ := copiedState.store enteredWF homes 13 (by rfl) 0
    128 (productArgs left right output) [] (body := fullBody)
  apply run_next_exists post found (by rfl) resetStep
  let k0 := rememberWord (rememberWord known 15 (localWord known 13)) 13 0
  apply run_local_word_call state0 originalCall enteredWF homes 15 9 13 15
    (localWord k0 15) (localWord k0 9) (countCarry (localWord k0 15) (localWord k0 9) 0)
    (localWord k0 15 + localWord k0 9) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state0.snapshots state0.call.1.1 13 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 15 9 13 15
  apply run_local_word_call state1 originalCall enteredWF homes 15 11 13 15
    (localWord k1 15) (localWord k1 11) (countCarry (localWord k1 15) (localWord k1 11) (localWord k1 13))
    (localWord k1 15 + localWord k1 11) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (by rfl)) post
  exact continuation

#print axioms full_middle_column
end UInt256Proof.Multiply.Safety
