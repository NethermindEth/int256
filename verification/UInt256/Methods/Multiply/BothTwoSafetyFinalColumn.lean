import UInt256.Methods.Multiply.BothTwoSafetyColumns

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def bothTwoFinalWords (original : Memory) (left right : Reference) :=
  let known := bothTwoSecondColumn original left right
  let reset := rememberWord (rememberWord known 11 (localWord known 7)) 7 0
  countWords (widenWords (countWords (countWords reset 11 5 7 11) 11 9 7 11) 1 2 13 12) 11 13 7 11

theorem both_two_final_column (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity bothTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (bothTwoSecondColumn original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (bothTwoFinalWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel bothTwoIndex 63 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 38 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  let known := bothTwoSecondColumn original left right
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (localWord known 7) (by rfl))
  obtain ⟨copied, copiedStep, copiedState⟩ := state.store enteredWF homes 11 (by rfl) (localWord known 7)
    39 (productArgs left right output) [] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) copiedStep
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, resetStep, state0⟩ := copiedState.store enteredWF homes 7 (by rfl) 0
    42 (productArgs left right output) [] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) resetStep
  let k0 := rememberWord (rememberWord known 11 (localWord known 7)) 7 0
  apply run_local_word_call state0 originalCall enteredWF homes 11 5 7 11
    (localWord k0 11) (localWord k0 5) (countCarry (localWord k0 11) (localWord k0 5) 0)
    (localWord k0 11 + localWord k0 5) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state0.snapshots state0.call.1.1 7 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 11 5 7 11
  apply run_local_word_call state1 originalCall enteredWF homes 11 9 7 11
    (localWord k1 11) (localWord k1 9) (countCarry (localWord k1 11) (localWord k1 9) (localWord k1 7))
    (localWord k1 11 + localWord k1 9) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 7 _ _ (localWord k1 7) (by rfl)) post
  intro m2 state2
  let k2 := countWords k1 11 9 7 11
  apply run_local_word_call state2 originalCall enteredWF homes 1 2 13 12
    (localWord k2 1) (localWord k2 2) (lowProduct (localWord k2 1) (localWord k2 2))
    (highProduct (localWord k2 1) (localWord k2 2)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract m2 _ _ state2.call.1.1 reference ready) post
  intro m3 state3
  let k3 := widenWords k2 1 2 13 12
  apply run_local_word_call state3 originalCall enteredWF homes 11 13 7 11
    (localWord k3 11) (localWord k3 13) (countCarry (localWord k3 11) (localWord k3 13) (localWord k3 7))
    (localWord k3 11 + localWord k3 13) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state3.snapshots state3.call.1.1 7 _ _ (localWord k3 7) (by rfl)) post
  exact continuation

#print axioms both_two_final_column
end UInt256Proof.Multiply.Safety
