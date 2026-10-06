import UInt256.Methods.Multiply.FullSafetySetup
import UInt256.Methods.Multiply.BothTwoSafetyColumns

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem localWord_known (known : Nat → Option (BitVec 64)) (index : Nat)
    (present : (known index).isSome = true) : known index = some (localWord known index) := by
  cases found : known index <;> simp_all [localWord]

def fullPrepared (original : Memory) (left right : Reference) :=
  rememberWord (fullInputs original left right) 6 (fullTop original left right)

def fullFirstProducts (original : Memory) (left right : Reference) :=
  widenWords (widenWords (widenWords (fullPrepared original left right) 0 1 8 7) 0 3 10 9) 2 1 12 11

def fullSecondColumn (original : Memory) (left right : Reference) :=
  countWords (countWords (rememberWord (fullFirstProducts original left right) 13 0) 7 10 13 14) 14 12 13 14

theorem full_second_column (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullPrepared original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullSecondColumn original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 124 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 96 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let k0 := fullPrepared original left right
  apply run_local_word_call state originalCall enteredWF homes 0 1 8 7
    (localWord k0 0) (localWord k0 1) (lowProduct (localWord k0 0) (localWord k0 1))
    (highProduct (localWord k0 0) (localWord k0 1)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 0 1 8 7
  apply run_local_word_call state1 originalCall enteredWF homes 0 3 10 9
    (localWord k1 0) (localWord k1 3) (lowProduct (localWord k1 0) (localWord k1 3))
    (highProduct (localWord k1 0) (localWord k1 3)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract m1 _ _ state1.call.1.1 reference ready) post
  intro m2 state2
  let k2 := widenWords k1 0 3 10 9
  apply run_local_word_call state2 originalCall enteredWF homes 2 1 12 11
    (localWord k2 2) (localWord k2 1) (lowProduct (localWord k2 2) (localWord k2 1))
    (highProduct (localWord k2 2) (localWord k2 1)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract m2 _ _ state2.call.1.1 reference ready) post
  intro m3 state3
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m4, reset, state4⟩ := state3.store enteredWF homes 13 (by rfl) 0
    113 (productArgs left right output) [] (body := fullBody)
  apply run_next_exists post found (by rfl) reset
  let k4 := rememberWord (fullFirstProducts original left right) 13 0
  apply run_local_word_call state4 originalCall enteredWF homes 7 10 13 14
    (localWord k4 7) (localWord k4 10) (countCarry (localWord k4 7) (localWord k4 10) 0)
    (localWord k4 7 + localWord k4 10) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state4.snapshots state4.call.1.1 13 _ _ 0 (by rfl)) post
  intro m5 state5
  let k5 := countWords k4 7 10 13 14
  apply run_local_word_call state5 originalCall enteredWF homes 14 12 13 14
    (localWord k5 14) (localWord k5 12) (countCarry (localWord k5 14) (localWord k5 12) (localWord k5 13))
    (localWord k5 14 + localWord k5 12) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state5.snapshots state5.call.1.1 13 _ _ (localWord k5 13) (by rfl)) post
  exact continuation

#print axioms full_second_column
end UInt256Proof.Multiply.Safety
