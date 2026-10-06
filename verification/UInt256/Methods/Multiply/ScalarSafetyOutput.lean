import UInt256.Methods.Multiply.ScalarSafetyPrefix
import UInt256.Methods.Multiply.CountCarry
import UInt256.Methods.Multiply.ScalarProduct
import UInt256.Methods.Multiply.StorageSafety
import UInt256.Methods.Multiply.ScalarValue
import UInt256.Safety.HalfRepresentation
import UInt256.Safety.OutputReturn

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

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def ladderWords (known : Nat → Option (BitVec 64)) (result : Nat) (low high incoming : BitVec 64) :=
  rememberWord (rememberWord (rememberWord known 5 low) result (low + incoming)) 3 (high + sumHigh low incoming)

def scalarProducts (original : Memory) (input : Reference) (word : BitVec 64) : Nat → Option (BitVec 64) :=
  ladderWords
    (ladderWords (scalarFirstProduct original input word) 6
      (lowProduct word (inputLimb original input 1)) (highProduct word (inputLimb original input 1))
      (highProduct word (inputLimb original input 0))) 7
    (lowProduct word (inputLimb original input 2)) (highProduct word (inputLimb original input 2))
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))

/-- Compose the original-input loads and three widening calls, including both
    carry updates. The untouched high input limb stays on the evaluation stack. -/
theorem scalar_products (contract : WordContract)
    (original entered current : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity scalarBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [input] [output] frame (scalarProducts original input word) →
      ∃ fuel final returned,
        run Extracted.program fuel scalarIndex 66 (scalarArgs input word output) frame
          [.scalar (.i64 (inputLimb original input 3))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 22 (scalarArgs input word output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply scalar_inputs original entered current input output word frame originalCall enteredWF homes state post
  intro prepared preparedState
  apply scalar_first_product contract original entered prepared input output word frame
    originalCall enteredWF homes preparedState post
  intro first firstState
  apply scalar_next_product false contract original entered first input output word (inputLimb original input 1)
    frame _ _ originalCall enteredWF homes firstState (by simp [ladderInput, scalarFirstProduct, scalarInputs, rememberWord]) post
  intro second secondState
  apply scalar_accumulate false original entered second input output word
    (lowProduct word (inputLimb original input 1)) (highProduct word (inputLimb original input 1))
    (highProduct word (inputLimb original input 0)) frame _ _ enteredWF homes secondState
    (by simp [rememberWord]) (by simp [rememberWord, scalarFirstProduct]) post
  intro summed summedState
  apply scalar_next_product true contract original entered summed input output word (inputLimb original input 2)
    frame _ _ originalCall enteredWF homes summedState
    (by simp [ladderInput, ladderResult, scalarFirstProduct, scalarInputs, rememberWord]) post
  intro third thirdState
  apply scalar_accumulate true original entered third input output word
    (lowProduct word (inputLimb original input 2)) (highProduct word (inputLimb original input 2))
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))
    frame _ _ enteredWF homes thirdState (by simp [rememberWord])
    (by simp [rememberWord, scalarCarry]) post
  exact continuation

#print axioms scalar_products
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

abbrev ScalarResult (original final : Memory) (input output : Reference)
    (word : BitVec 64) (returned : List Value) : Prop :=
  OutputResult original final output (inputValue original input * BitVec.ofNat 256 word.toNat) returned

theorem scalar_output (original entered current : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity scalarBody.localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame
      (scalarProducts original input word)) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 66 (scalarArgs input word output) frame
        [.scalar (.i64 (inputLimb original input 3))] current = .ok (final, returned) ∧
      ScalarResult original final input output word returned := by
  let words := scalarLimbs (inputLimb original input) word
  let carry := scalarCarry word (inputLimb original input 2)
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))
  let post := fun final returned => ScalarResult original final input output word returned
  have loadCarry := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := scalarBody) (args := scalarArgs input word output) (pc := pc) (stack := stack)
    (index := 3) carry (by simp [scalarProducts, ladderWords, rememberWord, carry, scalarCarry])
  obtain ⟨prepared, storedLast, preparedState⟩ := state.store enteredWF homes 8 (by rfl) (words 3)
    70 (scalarArgs input word output) [] (body := scalarBody)
  have lastValue : words 3 = inputLimb original input 3 * word + carry := by
    simp [words, scalarLimbs, CIL.fin_val_three, lowProduct, carry, BitVec.mul_comm]
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 4
    apply run_next_exists post found (by rfl)
    first
    | exact loadCarry _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, scalarArgs, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simpa only [lastValue] using storedLast
  have formed := preparedState.call.output_formed (by simp : output ∈ [output])
  have load (index : Fin 4) (pc : Nat) (stack : List Value) :
      step scalarBody (.local (if index = 0 then 4 else 5 + index.val)) pc
        (scalarArgs input word output) frame stack prepared =
        .ok (.next (pc + 1) (.scalar (.i64 (words index)) :: stack) frame prepared) := by
    apply preparedState.snapshots.load
    obtain ⟨i, bound⟩ := index
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [words, scalarLimbs, scalarProducts, ladderWords, scalarFirstProduct,
        scalarInputs, rememberWord, scalarCarry]
  iterate 5
    apply run_next_exists post found (by rfl)
    first
    | exact load 0 _ _
    | exact load 1 _ _
    | exact load 2 _ _
    | exact load 3 _ _
    | simp [step, scalarArgs, checkedValue, numericValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract prepared [input] output (words 0) (words 1) (words 2) (words 3) preparedState.call
  have stepped : step scalarBody (.call productStoreIndex 5) 76 (scalarArgs input word output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] prepared =
      .ok (.call productStoreIndex
        [.reference (.address output), .scalar (.i64 (words 0)), .scalar (.i64 (words 1)), .scalar (.i64 (words 2)),
          .scalar (.i64 (words 3))] [] prepared) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run Extracted.program 1 scalarIndex 77 (scalarArgs input word output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : scalarBody.code[77]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have mathematical := scalar_limbs_correct (inputLimb original input) word
  rw [input_limbs_value] at mathematical
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original prepared result [input] output _ frame
    originalCall valid owned preparedState.caller (packed.trans mathematical) readable outside⟩

#print axioms scalar_output
end UInt256Proof.Multiply.Safety
