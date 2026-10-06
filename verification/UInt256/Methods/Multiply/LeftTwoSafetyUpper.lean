import UInt256.Methods.Multiply.LeftTwoSafetyMiddle

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def leftTwoUpperProduct (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (leftTwoMiddleWords original left right)
    15 (lowProduct (inputLimb original left 0) (inputLimb original right 2)))
    14 (highProduct (inputLimb original left 0) (inputLimb original right 2))

theorem left_two_upper_product (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity leftTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (leftTwoMiddleWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (leftTwoUpperProduct original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel leftTwoIndex 70 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 66 (productArgs left right output) frame
        [.scalar (.i64 (inputLimb original left 0))] current = .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  obtain ⟨reference, slot, ready, formed⟩ := state.home enteredWF homes 15 (by rfl)
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (inputLimb original right 2) (by rfl))
  apply run_next_exists post found (by rfl)
  · simp [step, localAddress, slot, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state originalCall homes 15 reference
    (inputLimb original left 0) (inputLimb original right 2) slot ready post found (by rfl)
  · simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro middle middleState
  obtain ⟨after, stored, next⟩ := middleState.store enteredWF homes 14 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 2))
    69 (productArgs left right output) [] (body := leftTwoBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

def leftTwoUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (leftTwoUpperProduct original left right) 13 15 9 13
  rememberWord known 4 (localWord known 4 + localWord known 14)

theorem left_two_upper_accumulate
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity leftTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (leftTwoUpperProduct original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (leftTwoUpperWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel leftTwoIndex 79 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 70 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  let k0 := leftTwoUpperProduct original left right
  apply run_local_word_call state originalCall enteredWF homes 13 15 9 13
    (localWord k0 13) (localWord k0 15) (countCarry (localWord k0 13) (localWord k0 15) (localWord k0 9))
    (localWord k0 13 + localWord k0 15) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state.snapshots state.call.1.1 9 _ _ (localWord k0 9) (by rfl)) post
  intro middle middleState
  let k1 := countWords k0 13 15 9 13
  apply run_next_exists post found (by rfl) (middleState.snapshots.load (localWord k1 4) (by rfl))
  apply run_next_exists post found (by rfl) (middleState.snapshots.load (localWord k1 14) (by rfl))
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := middleState.store enteredWF homes 4 (by rfl)
    (localWord k1 4 + localWord k1 14) 78 (productArgs left right output) [] (body := leftTwoBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms left_two_upper_product
#print axioms left_two_upper_accumulate
end UInt256Proof.Multiply.Safety
