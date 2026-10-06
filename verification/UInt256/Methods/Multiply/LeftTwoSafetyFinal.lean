import UInt256.Methods.Multiply.LeftTwoSafetyUpper

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def leftTwoFinalWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (leftTwoUpperWords original left right) 0 2 17 16) 13 17 9 13
  rememberWord known 4 (localWord known 4 + (localWord known 16 + localWord known 9))

theorem left_two_final (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity leftTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (leftTwoUpperWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (leftTwoFinalWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel leftTwoIndex 95 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 79 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  let k0 := leftTwoUpperWords original left right
  apply run_local_word_call state originalCall enteredWF homes 0 2 17 16
    (localWord k0 0) (localWord k0 2) (lowProduct (localWord k0 0) (localWord k0 2))
    (highProduct (localWord k0 0) (localWord k0 2)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 0 2 17 16
  apply run_local_word_call state1 originalCall enteredWF homes 13 17 9 13
    (localWord k1 13) (localWord k1 17) (countCarry (localWord k1 13) (localWord k1 17) (localWord k1 9))
    (localWord k1 13 + localWord k1 17) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 9 _ _ (localWord k1 9) (by rfl)) post
  intro m2 state2
  let k2 := countWords k1 13 17 9 13
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 4) (by rfl))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 16) (by rfl))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 9) (by rfl))
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 4 (by rfl)
    (localWord k2 4 + (localWord k2 16 + localWord k2 9)) 94 (productArgs left right output) [] (body := leftTwoBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms left_two_final
end UInt256Proof.Multiply.Safety
