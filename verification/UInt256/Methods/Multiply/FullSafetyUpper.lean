import UInt256.Methods.Multiply.FullSafetyMiddle

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullFirstUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullMiddleWords original left right) 0 5 17 16) 15 17 13 15
  rememberWord known 6 (localWord known 6 + localWord known 16)

theorem full_first_upper (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullMiddleWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullFirstUpperWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 153 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 139 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let k0 := fullMiddleWords original left right
  apply run_local_word_call state originalCall enteredWF homes 0 5 17 16
    (localWord k0 0) (localWord k0 5) (lowProduct (localWord k0 0) (localWord k0 5))
    (highProduct (localWord k0 0) (localWord k0 5))
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 0 5 17 16
  apply run_local_word_call state1 originalCall enteredWF homes 15 17 13 15
    (localWord k1 15) (localWord k1 17) (countCarry (localWord k1 15) (localWord k1 17) (localWord k1 13))
    (localWord k1 15 + localWord k1 17)
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
  intro m2 state2
  let k2 := countWords k1 15 17 13 15
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 16) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
    (localWord k2 6 + localWord k2 16) 152 (productArgs left right output) [] (body := fullBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms full_first_upper

def fullUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullFirstUpperWords original left right) 2 3 19 18) 15 19 13 15
  rememberWord known 6 (localWord known 6 + localWord known 18)

theorem full_upper (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullFirstUpperWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullUpperWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 167 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 153 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let k0 := fullFirstUpperWords original left right
  apply run_local_word_call state originalCall enteredWF homes 2 3 19 18
    (localWord k0 2) (localWord k0 3) (lowProduct (localWord k0 2) (localWord k0 3))
    (highProduct (localWord k0 2) (localWord k0 3))
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 2 3 19 18
  apply run_local_word_call state1 originalCall enteredWF homes 15 19 13 15
    (localWord k1 15) (localWord k1 19) (countCarry (localWord k1 15) (localWord k1 19) (localWord k1 13))
    (localWord k1 15 + localWord k1 19)
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
  intro m2 state2
  let k2 := countWords k1 15 19 13 15
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 18) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
    (localWord k2 6 + localWord k2 18) 166 (productArgs left right output) [] (body := fullBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms full_upper

end UInt256Proof.Multiply.Safety
