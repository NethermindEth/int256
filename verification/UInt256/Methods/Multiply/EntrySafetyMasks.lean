import UInt256.Methods.Multiply.EntrySafetySetup

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def inputUpper (memory : Memory) (input : Reference) :=
  inputLimb memory input 2 ||| inputLimb memory input 3

theorem multiply_upper_mask (rightSide : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame known)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord known (if rightSide then 3 else 2) (inputUpper original (if rightSide then right else left))) →
      ∃ fuel final returned,
        run Extracted.program fuel multiplyIndex (if rightSide then 18 else 12)
          (productArgs left right output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex (if rightSide then 12 else 6)
        (productArgs left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
  let input := if rightSide then right else left
  let pc := if rightSide then 12 else 6
  let index := if rightSide then 3 else 2
  have member : input ∈ [left, right] := by cases rightSide <;> simp [input]
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have formed := state.call.input_formed member
  have reading2 := state.input_field originalCall input member 2
  have reading3 := state.input_field originalCall input member 3
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes index (by cases rightSide <;> rfl)
    (inputUpper original input) (pc + 5) (productArgs left right output) [] (body := multiplyBody)
  cases rightSide <;> dsimp [input, pc, index] at formed reading2 reading3 stored next continuation ⊢
  all_goals
    iterate 5
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, pureArity, productArgs, checkedValue, numericValue, formValue, formed, reading2, reading3,
          checkedAt, scalars, CIL.step, CIL.binary, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored (continuation after next)

def inputTail (memory : Memory) (input : Reference) :=
  inputLimb memory input 1 ||| inputUpper memory input

theorem multiply_tail_mask (rightSide : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame known)
    (knownUpper : known (if rightSide then 3 else 2) = some (inputUpper original (if rightSide then right else left)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord known (if rightSide then 5 else 4) (inputTail original (if rightSide then right else left))) →
      ∃ fuel final returned,
        run Extracted.program fuel multiplyIndex (if rightSide then 28 else 23)
          (productArgs left right output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex (if rightSide then 23 else 18)
        (productArgs left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
  let input := if rightSide then right else left
  let pc := if rightSide then 23 else 18
  let index := if rightSide then 5 else 4
  have member : input ∈ [left, right] := by cases rightSide <;> simp [input]
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have formed := state.call.input_formed member
  have reading := state.input_field originalCall input member 1
  have loadUpper := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (inputUpper original input) knownUpper
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes index (by cases rightSide <;> rfl)
    (inputTail original input) (pc + 4) (productArgs left right output) [] (body := multiplyBody)
  cases rightSide <;> dsimp [input, pc, index] at formed reading loadUpper stored next continuation ⊢
  all_goals
    iterate 4
      apply run_next_exists post found (by rfl)
      first
      | exact loadUpper _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, pureArity, productArgs, checkedValue, numericValue, formValue, formed, reading,
            checkedAt, scalars, CIL.step, CIL.binary, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms multiply_upper_mask
#print axioms multiply_tail_mask
end UInt256Proof.Multiply.Safety
