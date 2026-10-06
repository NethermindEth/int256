import UInt256.Methods.Multiply.ScalarSafetyPrefix
import UInt256.Methods.Multiply.CountCarry

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def ladderStart (second : Bool) : Nat := if second then 52 else 38
def ladderInput (second : Bool) : Nat := if second then 2 else 1
def ladderResult (second : Bool) : Nat := if second then 7 else 6

/-- Both subsequent widening calls share one checked execution proof. -/
theorem scalar_next_product (second : Bool) (contract : WordContract)
    (original entered current : Memory) (input output : Reference) (word limb : BitVec 64)
    (frame : Frame) (known : Nat → Option (BitVec 64)) (rest : List Value)
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity scalarBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame known)
    (saved : known (ladderInput second) = some limb)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [input] [output] frame
        (rememberWord known 5 (lowProduct word limb)) →
      ∃ fuel final returned,
        run Extracted.program fuel scalarIndex (ladderStart second + 4) (scalarArgs input word output) frame
          (.scalar (.i64 (highProduct word limb)) :: rest) after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex (ladderStart second) (scalarArgs input word output) frame rest current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, slot, _, ready⟩ := homes.home_at 5 .word64 (by rfl)
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have writable := state.authority.access ready (enteredWF.1 _ _ requirements.present).1
  have formed := access_reference_valid _ _ _ _ _ writable
  have load := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := scalarBody) (args := scalarArgs input word output) (pc := pc) (stack := stack) limb saved
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  cases second
  all_goals
    dsimp [ladderStart, ladderInput] at load continuation ⊢
    iterate 3
      apply run_next_exists post found (by rfl)
      first
      | exact load _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, scalarArgs, checkedValue, numericValue, formValue, localAddress, slot, formed,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_word_call contract state originalCall homes 5 reference word limb slot writable post found (by rfl)
    · simp [step, checkedValue, numericValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl⟩
    exact continuation

/-- Add a saved low product to the incoming carry, initialize the next result
    limb, and replace the carry by the high word plus the exact overflow bit. -/
theorem scalar_accumulate (second : Bool)
    (original entered current : Memory) (input output : Reference) (word low high incoming : BitVec 64)
    (frame : Frame) (known : Nat → Option (BitVec 64)) (rest : List Value)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity scalarBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame known)
    (savedLow : known 5 = some low) (savedCarry : known 3 = some incoming)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [input] [output] frame
        (rememberWord (rememberWord known (ladderResult second) (low + incoming)) 3 (high + sumHigh low incoming)) →
      ∃ fuel final returned,
        run Extracted.program fuel scalarIndex (ladderStart second + 14) (scalarArgs input word output) frame
          rest after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex (ladderStart second + 4) (scalarArgs input word output) frame
        (.scalar (.i64 high) :: rest) current = .ok (final, returned) ∧ post final returned := by
  have specified : scalarBody.localKinds[ladderResult second]? = some .word64 := by cases second <;> rfl
  obtain ⟨middle, storeResult, resultState⟩ := state.store enteredWF homes (ladderResult second) specified
    (low + incoming) (ladderStart second + 7) (scalarArgs input word output) (.scalar (.i64 high) :: rest)
      (body := scalarBody)
  obtain ⟨after, storeCarry, carryState⟩ := resultState.store enteredWF homes 3 (by rfl)
    (high + sumHigh low incoming) (ladderStart second + 13) (scalarArgs input word output) rest
      (body := scalarBody)
  have done := continuation after carryState
  have loadLow := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := scalarBody) (args := scalarArgs input word output) (pc := pc) (stack := stack) low savedLow
  have loadCarry := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := scalarBody) (args := scalarArgs input word output) (pc := pc) (stack := stack) incoming savedCarry
  have loadResult := fun (pc : Nat) (stack : List Value) => resultState.snapshots.load
    (body := scalarBody) (args := scalarArgs input word output) (pc := pc) (stack := stack)
    (index := ladderResult second) (low + incoming) (by simp [rememberWord])
  have remainingLow : rememberWord known (ladderResult second) (low + incoming) 5 = some low := by
    cases second <;> simpa [ladderResult, rememberWord] using savedLow
  have loadLowAgain := fun (pc : Nat) (stack : List Value) => resultState.snapshots.load
    (body := scalarBody) (args := scalarArgs input word output) (pc := pc) (stack := stack) low remainingLow
  have flag : BitVec.signExtend 64
      (if low + incoming < low then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) = sumHigh low incoming := by
    rw [← sumHigh_flag]
    split <;> rfl
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  cases second
  all_goals
    dsimp [ladderStart, ladderResult] at storeResult storeCarry loadResult done ⊢
    iterate 3
      apply run_next_exists post found (by rfl)
      first
      | exact loadLow _ _
      | exact loadCarry _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists post found (by rfl) storeResult
    iterate 5
      apply run_next_exists post found (by rfl)
      first
      | exact loadResult _ _
      | exact loadLowAgain _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists post found (by rfl)
    · simpa only [← flag] using storeCarry
    exact done

#print axioms scalar_next_product
#print axioms scalar_accumulate
end UInt256Proof.Multiply.Safety
