import UInt256.Methods.Multiply.FullSafetySetup

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem full_scalar_top
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord (fullInputs original left right) 6 (fullTop original left right)) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 96 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 18 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have profile : fullBody.profile = Extracted.profile := by rfl
  iterate 4
    apply run_next_exists post found (by rfl)
    simp [step, profile, Extracted.profile, CIL.FeatureProfile.evaluate,
      pureArity, scalars, CIL.step.eq_def, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have formedRight := state.call.input_formed (by simp : right ∈ [left, right])
  have readingLeft := state.input_field originalCall left (by simp) 3
  have readingRight := state.input_field originalCall right (by simp) 3
  have load0 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 0) (inputLimb original left 0) (by rfl)
  have load1 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 1) (inputLimb original right 0) (by rfl)
  have load2 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 2) (inputLimb original left 1) (by rfl)
  have load3 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 3) (inputLimb original right 1) (by rfl)
  have load4 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 4) (inputLimb original left 2) (by rfl)
  have load5 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 5) (inputLimb original right 2) (by rfl)
  iterate 17
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | exact load1 _ _
    | exact load2 _ _
    | exact load3 _ _
    | exact load4 _ _
    | exact load5 _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, pureArity, productArgs, checkedValue, numericValue, formValue, formedLeft, formedRight,
          readingLeft, readingRight, checkedAt, scalars, CIL.step.eq_def, CIL.binary,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes 6 (by rfl) (fullTop original left right)
    95 (productArgs left right output) [] (body := fullBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms full_scalar_top
end UInt256Proof.Multiply.Safety
