import UInt256.Methods.Multiply.FullSafetyUpper

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullFinalWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullUpperWords original left right) 4 1 21 20) 15 21 13 15
  rememberWord known 6 (localWord known 6 + (localWord known 20 + localWord known 13))

theorem full_final (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullUpperWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullFinalWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 183 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 167 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let k0 := fullUpperWords original left right
  apply run_local_word_call state originalCall enteredWF homes 4 1 21 20
    (localWord k0 4) (localWord k0 1) (lowProduct (localWord k0 4) (localWord k0 1))
    (highProduct (localWord k0 4) (localWord k0 1)) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 4 1 21 20
  apply run_local_word_call state1 originalCall enteredWF homes 15 21 13 15
    (localWord k1 15) (localWord k1 21) (countCarry (localWord k1 15) (localWord k1 21) (localWord k1 13))
    (localWord k1 15 + localWord k1 21) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
  intro m2 state2
  let k2 := countWords k1 15 21 13 15
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 20) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 13) (localWord_known _ _ (by rfl)))
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
    (localWord k2 6 + (localWord k2 20 + localWord k2 13)) 182 (productArgs left right output) [] (body := fullBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms full_final
end UInt256Proof.Multiply.Safety
