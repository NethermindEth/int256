import UInt256.Methods.Multiply.BothTwoSafetySetup

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
