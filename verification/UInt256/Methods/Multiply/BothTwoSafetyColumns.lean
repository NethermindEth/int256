import UInt256.Methods.Multiply.BothTwoSafetySetup
import UInt256.Methods.Multiply.LocalArithmeticSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def bothTwoFirstProducts (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (bothTwoInputs original left right)
    4 (lowProduct (inputLimb original left 0) (inputLimb original right 0)))
    3 (highProduct (inputLimb original left 0) (inputLimb original right 0)))
    6 (lowProduct (inputLimb original left 0) (inputLimb original right 1)))
    5 (highProduct (inputLimb original left 0) (inputLimb original right 1))

theorem both_two_first_products (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity bothTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (bothTwoInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (bothTwoFirstProducts original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel bothTwoIndex 20 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 11 (productArgs left right output) frame
        [.scalar (.i64 (inputLimb original left 0))] current = .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  obtain ⟨low0, slot0, ready0, formed0⟩ := state.home enteredWF homes 4 (by rfl)
  have load0 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := bothTwoBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 0) (inputLimb original right 0) (by simp [bothTwoInputs, rememberWord])
  iterate 3
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | simp [step, pureArity, instruction, localAddress, slot0, formValue, formed0, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state originalCall homes 4 low0
    (inputLimb original left 0) (inputLimb original right 0) slot0 ready0 post found (by rfl)
  · simp [step, checkedValue, numericValue, formValue, formed0, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  intro m0 state0
  obtain ⟨m1, stored0, state1⟩ := state0.store enteredWF homes 3 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 0))
    15 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) stored0
  obtain ⟨low1, slot1, ready1, formed1⟩ := state1.home enteredWF homes 6 (by rfl)
  have load1 := fun (pc : Nat) (stack : List Value) => state1.snapshots.load
    (body := bothTwoBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 2) (inputLimb original right 1) (by simp [bothTwoInputs, rememberWord])
  iterate 2
    apply run_next_exists post found (by rfl)
    first
    | exact load1 _ _
    | simp [step, localAddress, slot1, formValue, formed1, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state1 originalCall homes 6 low1
    (inputLimb original left 0) (inputLimb original right 1) slot1 ready1 post found (by rfl)
  · simp [step, checkedValue, numericValue, formValue, formed1, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro m2 state2
  obtain ⟨m3, stored1, state3⟩ := state2.store enteredWF homes 5 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 1))
    19 (productArgs left right output) [] (body := bothTwoBody)
  exact run_next_exists post found (by rfl) stored1 (continuation m3 state3)

#print axioms both_two_first_products
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

/-- A notation for arithmetic expressions, not evidence that a local is readable.
    Every execution use separately proves `known index = some value`. -/
def localWord (known : Nat → Option (BitVec 64)) (index : Nat) : BitVec 64 := (known index).getD 0

def widenWords (known : Nat → Option (BitVec 64)) (left right target result : Nat) :=
  rememberWord (rememberWord known target (lowProduct (localWord known left) (localWord known right)))
    result (highProduct (localWord known left) (localWord known right))

def countWords (known : Nat → Option (BitVec 64)) (left right counter result : Nat) :=
  rememberWord (rememberWord known counter
    (countCarry (localWord known left) (localWord known right) (localWord known counter)))
    result (localWord known left + localWord known right)

def bothTwoSecondColumn (original : Memory) (left right : Reference) :=
  countWords (widenWords (countWords (rememberWord (bothTwoFirstProducts original left right) 7 0)
    3 6 7 8) 1 0 10 9) 8 10 7 8

theorem both_two_second_column (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity bothTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (bothTwoFirstProducts original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (bothTwoSecondColumn original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel bothTwoIndex 38 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 20 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, stored, state0⟩ := state.store enteredWF homes 7 (by rfl) 0
    22 (productArgs left right output) [] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) stored
  let k0 := rememberWord (bothTwoFirstProducts original left right) 7 0
  apply run_local_word_call state0 originalCall enteredWF homes 3 6 7 8
    (localWord k0 3) (localWord k0 6) (countCarry (localWord k0 3) (localWord k0 6) 0)
    (localWord k0 3 + localWord k0 6) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state0.snapshots state0.call.1.1 7 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 3 6 7 8
  apply run_local_word_call state1 originalCall enteredWF homes 1 0 10 9
    (localWord k1 1) (localWord k1 0) (lowProduct (localWord k1 1) (localWord k1 0))
    (highProduct (localWord k1 1) (localWord k1 0)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract m1 _ _ state1.call.1.1 reference ready) post
  intro m2 state2
  let k2 := widenWords k1 1 0 10 9
  apply run_local_word_call state2 originalCall enteredWF homes 8 10 7 8
    (localWord k2 8) (localWord k2 10) (countCarry (localWord k2 8) (localWord k2 10) (localWord k2 7))
    (localWord k2 8 + localWord k2 10) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state2.snapshots state2.call.1.1 7 _ _ (localWord k2 7) (by rfl)) post
  exact continuation

#print axioms both_two_second_column
end UInt256Proof.Multiply.Safety
