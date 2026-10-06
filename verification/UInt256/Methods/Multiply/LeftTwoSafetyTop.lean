import UInt256.Methods.Multiply.LeftTwoSafetySetup

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def leftTwoTop (original : Memory) (left right : Reference) :=
  inputLimb original left 0 * inputLimb original right 3 + inputLimb original left 1 * inputLimb original right 2

theorem left_two_top (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity leftTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (leftTwoInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord (leftTwoInputs original left right) 4 (leftTwoTop original left right)) →
      ∃ fuel final returned,
        run Extracted.program fuel leftTwoIndex 23 (productArgs left right output) frame
          [.scalar (.i64 (inputLimb original left 0))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 14 (productArgs left right output) frame
        [.scalar (.i64 (inputLimb original left 0))] current = .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  have formed := state.call.input_formed (by simp : right ∈ [left, right])
  have reading := state.input_field originalCall right (by simp) 3
  have load0 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := leftTwoBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 0) (inputLimb original left 1) (by rfl)
  have load3 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := leftTwoBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 3) (inputLimb original right 2) (by rfl)
  apply run_next_exists post found (by rfl) (by rfl)
  iterate 7
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | exact load3 _ _
    | simp [step, pureArity, productArgs, checkedValue, numericValue, formValue, formed,
        reading, checkedAt, scalars, CIL.step, CIL.binary,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes 4 (by rfl) (leftTwoTop original left right)
    22 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := leftTwoBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms left_two_top
end UInt256Proof.Multiply.Safety
