import UInt256.Methods.Multiply.LeftTwoSafetyPrefix
import UInt256.Methods.Multiply.BothTwoSafetyColumns

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def leftTwoSecondColumn (original : Memory) (left right : Reference) :=
  countWords (widenWords (countWords (rememberWord (leftTwoFirstProducts original left right) 9 0)
    5 8 9 10) 0 1 12 11) 10 12 9 10

theorem left_two_second_column (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity leftTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (leftTwoFirstProducts original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (leftTwoSecondColumn original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel leftTwoIndex 51 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 33 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, stored, state0⟩ := state.store enteredWF homes 9 (by rfl) 0
    35 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := leftTwoBody)
  apply run_next_exists post found (by rfl) stored
  let k0 := rememberWord (leftTwoFirstProducts original left right) 9 0
  apply run_local_word_call state0 originalCall enteredWF homes 5 8 9 10
    (localWord k0 5) (localWord k0 8) (countCarry (localWord k0 5) (localWord k0 8) 0)
    (localWord k0 5 + localWord k0 8) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state0.snapshots state0.call.1.1 9 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 5 8 9 10
  apply run_local_word_call state1 originalCall enteredWF homes 0 1 12 11
    (localWord k1 0) (localWord k1 1) (lowProduct (localWord k1 0) (localWord k1 1))
    (highProduct (localWord k1 0) (localWord k1 1)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract m1 _ _ state1.call.1.1 reference ready) post
  intro m2 state2
  let k2 := widenWords k1 0 1 12 11
  apply run_local_word_call state2 originalCall enteredWF homes 10 12 9 10
    (localWord k2 10) (localWord k2 12) (countCarry (localWord k2 10) (localWord k2 12) (localWord k2 9))
    (localWord k2 10 + localWord k2 12) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state2.snapshots state2.call.1.1 9 _ _ (localWord k2 9) (by rfl)) post
  exact continuation

#print axioms left_two_second_column
end UInt256Proof.Multiply.Safety
