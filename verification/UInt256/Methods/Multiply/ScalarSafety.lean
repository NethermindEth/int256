import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Safety.PrivateInputValues
import UInt256.Methods.Multiply.Calls
import UInt256.Methods.Multiply.ScalarProduct
import UInt256.Methods.Multiply.ScalarValue
import UInt256.Methods.Multiply.ProductStorage
import UInt256.Safety.ArgumentValues
import UInt256.Safety.OutputReturn
import CIL.Safety.MethodContract

namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def scalarBody (profile : CIL.FeatureProfile) (wordIndex storageIndex : Nat) : CIL.Method := { profile := profile, returnsValue := false, locals := [.unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64], parameterHomes := [], staticSites := [], code := [
  .arg 1,
  .const32 1,
  .convI8,
  .bgtu 22,
  .arg 1,
  .brnonzero 17,
  .arg 2,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .call storageIndex 5,
  .ret,
  .arg 2,
  .arg 0,
  .loadAggregate 32,
  .storeAggregate 32,
  .ret,
  .arg 0,
  .fieldAt 0 8,
  .setLocal 0,
  .arg 0,
  .fieldAt 8 8,
  .setLocal 1,
  .arg 0,
  .fieldAt 16 8,
  .setLocal 2,
  .arg 0,
  .fieldAt 24 8,
  .arg 1,
  .local 0,
  .localAddr 4,
  .call wordIndex 3,
  .setLocal 3,
  .arg 1,
  .local 1,
  .localAddr 5,
  .call wordIndex 3,
  .local 5,
  .local 3,
  .add,
  .setLocal 6,
  .local 6,
  .local 5,
  .ltu,
  .convI8,
  .add,
  .setLocal 3,
  .arg 1,
  .local 2,
  .localAddr 5,
  .call wordIndex 3,
  .local 5,
  .local 3,
  .add,
  .setLocal 7,
  .local 7,
  .local 5,
  .ltu,
  .convI8,
  .add,
  .setLocal 3,
  .arg 1,
  .mul,
  .local 3,
  .add,
  .setLocal 8,
  .arg 2,
  .local 4,
  .local 6,
  .local 7,
  .local 8,
  .call storageIndex 5,
  .ret] }
def scalarArgs (input : Reference) (word : BitVec 64) (output : Reference) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

theorem scalar_frame_setup (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (_found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program memory [input] [output]) :
    ∃ frame entered,
      enterFrame (scalarBody profile wordIndex storageIndex) (scalarArgs input word output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords program memory entered entered [input] [output] frame (fun _ => none) := by
  have kinds : (scalarBody profile wordIndex storageIndex).localKinds = List.replicate 9 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (scalarBody profile wordIndex storageIndex)
    (by rfl) (by simp [kinds]) (by simp [kinds]) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (scalarArgs input word output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

/-- Each input limb is loaded from the original caller bytes before being
    written to a previously unknown private home. -/
theorem scalar_input_save (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (original entered current : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame) (known : Nat → Option (BitVec 64)) (index : Fin 3)
    (originalCall : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [input] [output] frame known)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [input] [output] frame
        (rememberWord known index.val (inputLimb original input ⟨index.val, by omega⟩)) →
      ∃ fuel final returned,
        run program fuel methodIndex (25 + 3 * index.val)
          (scalarArgs input word output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex (22 + 3 * index.val)
        (scalarArgs input word output) frame [] current = .ok (final, returned) ∧ post final returned := by
  have specified : (scalarBody profile wordIndex storageIndex).localKinds[index.val]? = some .word64 := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl
  obtain ⟨after, stored, updated⟩ := state.store enteredWF homes index.val specified
    (inputLimb original input ⟨index.val, by omega⟩) (24 + 3 * index.val) (scalarArgs input word output) []
      (body := (scalarBody profile wordIndex storageIndex))
  have done := continuation after updated
  have formed := state.call.input_formed (by simp : input ∈ [input])
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (originalCall.input_formed (by simp : input ∈ [input]))
  have old := (originalCall.1.1.1 _ _ present).1
  have bytes : (fun offset => (current.cells input.allocation offset).bits) =
      (fun offset => (original.cells input.allocation offset).bits) := by
    funext offset
    rw [state.caller input.allocation old offset]
  have reading (rest : List Value) :
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address input) :: rest) current =
        .ok (current, .scalar (.i64 (inputLimb original input ⟨index.val, by omega⟩)) :: rest) := by
    simpa [inputLimb, bytes, CIL.fin_val_three] using state.call.input_field_instruction (by simp : input ∈ [input]) (⟨index.val, by omega⟩ : Fin 4) rest
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp at reading stored done
    iterate 2
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, cil_guard, observerCount, pureArity, scalarArgs, checkedValue, formValue, formed, reading,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored done

#print axioms scalar_frame_setup
#print axioms scalar_input_save
end UInt256Proof.Multiply.ScalarSafety

namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def scalarInputs (original : Memory) (input : Reference) : Nat → Option (BitVec 64) :=
  rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original input 0)) 1 (inputLimb original input 1)) 2 (inputLimb original input 2)

def scalarFirstProduct (original : Memory) (input : Reference) (word : BitVec 64) : Nat → Option (BitVec 64) :=
  rememberWord (rememberWord (scalarInputs original input)
    4 (lowProduct word (inputLimb original input 0))) 3 (highProduct word (inputLimb original input 0))

theorem scalar_inputs (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (original entered current : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [input] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [input] [output] frame (scalarInputs original input) →
      ∃ fuel final returned,
        run program fuel methodIndex 31 (scalarArgs input word output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex 22 (scalarArgs input word output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply scalar_input_save profile program methodIndex wordIndex storageIndex found original entered current input output word frame _ 0 originalCall enteredWF homes state post
  intro m0 state0
  apply scalar_input_save profile program methodIndex wordIndex storageIndex found original entered m0 input output word frame _ 1 originalCall enteredWF homes state0 post
  intro m1 state1
  apply scalar_input_save profile program methodIndex wordIndex storageIndex found original entered m1 input output word frame _ 2 originalCall enteredWF homes state1 post
  exact continuation

/-- Keep the fourth original limb on the evaluation stack while the first
    widening call initializes the low-product home and the incoming carry. -/
theorem scalar_first_product (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [input] [output] frame (scalarInputs original input))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [input] [output] frame (scalarFirstProduct original input word) →
      ∃ fuel final returned,
        run program fuel methodIndex 38 (scalarArgs input word output) frame
          [.scalar (.i64 (inputLimb original input 3))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex 31 (scalarArgs input word output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, slot, _, ready⟩ := homes.home_at 4 .word64 (by rfl)
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have writable := state.authority.access ready (enteredWF.1 _ _ requirements.present).1
  have referenceFormed := access_reference_valid _ _ _ _ _ writable
  have inputFormed := state.call.input_formed (by simp : input ∈ [input])
  obtain ⟨inputAllocation, inputPresent, _, _⟩ := formed_reference_live _ _ _
    (originalCall.input_formed (by simp : input ∈ [input]))
  have inputOld := (originalCall.1.1.1 _ _ inputPresent).1
  have bytes : (fun offset => (current.cells input.allocation offset).bits) =
      (fun offset => (original.cells input.allocation offset).bits) := by
    funext offset
    rw [state.caller input.allocation inputOld offset]
  have reading (rest : List Value) : instruction (.fieldAt 24 8) (.reference (.address input) :: rest) current =
      .ok (current, .scalar (.i64 (inputLimb original input 3)) :: rest) := by
    simpa [inputLimb, bytes, CIL.fin_val_three] using state.call.input_field_instruction (by simp : input ∈ [input]) (3 : Fin 4) rest
  have load0 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (scalarBody profile wordIndex storageIndex)) (args := scalarArgs input word output) (pc := pc) (stack := stack)
    (index := 0) (inputLimb original input 0) (by simp [scalarInputs, rememberWord])
  iterate 5
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, cil_guard, observerCount, pureArity, scalarArgs, checkedValue, numericValue, formValue, inputFormed,
          localAddress, slot, referenceFormed, reading, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state originalCall homes 4 reference word (inputLimb original input 0)
    slot writable post found (by rfl)
  · simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, referenceFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro middle middleState
  obtain ⟨after, stored, finalState⟩ := middleState.store enteredWF homes 3 (by rfl)
    (highProduct word (inputLimb original input 0)) 37 (scalarArgs input word output)
    [.scalar (.i64 (inputLimb original input 3))] (body := (scalarBody profile wordIndex storageIndex))
  exact run_next_exists post found (by rfl) stored (continuation after finalState)

#print axioms scalar_inputs
#print axioms scalar_first_product
end UInt256Proof.Multiply.ScalarSafety
namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def ladderStart (second : Bool) : Nat := if second then 52 else 38
def ladderInput (second : Bool) : Nat := if second then 2 else 1
def ladderResult (second : Bool) : Nat := if second then 7 else 6

/-- Both subsequent widening calls share one checked execution proof. -/
theorem scalar_next_product (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (second : Bool) (contract : WordContract program wordIndex)
    (original entered current : Memory) (input output : Reference) (word limb : BitVec 64)
    (frame : Frame) (known : Nat → Option (BitVec 64)) (rest : List Value)
    (originalCall : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [input] [output] frame known)
    (saved : known (ladderInput second) = some limb)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [input] [output] frame
        (rememberWord known 5 (lowProduct word limb)) →
      ∃ fuel final returned,
        run program fuel methodIndex (ladderStart second + 4) (scalarArgs input word output) frame
          (.scalar (.i64 (highProduct word limb)) :: rest) after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex (ladderStart second) (scalarArgs input word output) frame rest current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, slot, _, ready⟩ := homes.home_at 5 .word64 (by rfl)
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have writable := state.authority.access ready (enteredWF.1 _ _ requirements.present).1
  have formed := access_reference_valid _ _ _ _ _ writable
  have load := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (scalarBody profile wordIndex storageIndex)) (args := scalarArgs input word output) (pc := pc) (stack := stack) limb saved
  cases second
  all_goals
    dsimp [ladderStart, ladderInput] at load continuation ⊢
    iterate 3
      apply run_next_exists post found (by rfl)
      first
      | exact load _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, cil_guard, observerCount, scalarArgs, checkedValue, numericValue, formValue, localAddress, slot, formed,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_word_call contract state originalCall homes 5 reference word limb slot writable post found (by rfl)
    · simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl⟩
    exact continuation

/-- Add a saved low product to the incoming carry, initialize the next result
    limb, and replace the carry by the high word plus the exact overflow bit. -/
theorem scalar_accumulate (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (second : Bool)
    (original entered current : Memory) (input output : Reference) (word low high incoming : BitVec 64)
    (frame : Frame) (known : Nat → Option (BitVec 64)) (rest : List Value)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [input] [output] frame known)
    (savedLow : known 5 = some low) (savedCarry : known 3 = some incoming)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [input] [output] frame
        (rememberWord (rememberWord known (ladderResult second) (low + incoming)) 3 (high + sumHigh low incoming)) →
      ∃ fuel final returned,
        run program fuel methodIndex (ladderStart second + 14) (scalarArgs input word output) frame
          rest after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex (ladderStart second + 4) (scalarArgs input word output) frame
        (.scalar (.i64 high) :: rest) current = .ok (final, returned) ∧ post final returned := by
  have specified : (scalarBody profile wordIndex storageIndex).localKinds[ladderResult second]? = some .word64 := by cases second <;> rfl
  obtain ⟨middle, storeResult, resultState⟩ := state.store enteredWF homes (ladderResult second) specified
    (low + incoming) (ladderStart second + 7) (scalarArgs input word output) (.scalar (.i64 high) :: rest)
      (body := (scalarBody profile wordIndex storageIndex))
  obtain ⟨after, storeCarry, carryState⟩ := resultState.store enteredWF homes 3 (by rfl)
    (high + sumHigh low incoming) (ladderStart second + 13) (scalarArgs input word output) rest
      (body := (scalarBody profile wordIndex storageIndex))
  have done := continuation after carryState
  have loadLow := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (scalarBody profile wordIndex storageIndex)) (args := scalarArgs input word output) (pc := pc) (stack := stack) low savedLow
  have loadCarry := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (scalarBody profile wordIndex storageIndex)) (args := scalarArgs input word output) (pc := pc) (stack := stack) incoming savedCarry
  have loadResult := fun (pc : Nat) (stack : List Value) => resultState.snapshots.load
    (body := (scalarBody profile wordIndex storageIndex)) (args := scalarArgs input word output) (pc := pc) (stack := stack)
    (index := ladderResult second) (low + incoming) (by simp [rememberWord])
  have remainingLow : rememberWord known (ladderResult second) (low + incoming) 5 = some low := by
    cases second <;> simpa [ladderResult, rememberWord] using savedLow
  have loadLowAgain := fun (pc : Nat) (stack : List Value) => resultState.snapshots.load
    (body := (scalarBody profile wordIndex storageIndex)) (args := scalarArgs input word output) (pc := pc) (stack := stack) low remainingLow
  have flag : BitVec.signExtend 64
      (if low + incoming < low then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) = sumHigh low incoming := by
    rw [← sumHigh_flag]
    split <;> rfl
  cases second
  all_goals
    dsimp [ladderStart, ladderResult] at storeResult storeCarry loadResult done ⊢
    iterate 3
      apply run_next_exists post found (by rfl)
      first
      | exact loadLow _ _
      | exact loadCarry _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, cil_guard, observerCount, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.binary,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists post found (by rfl) storeResult
    iterate 5
      apply run_next_exists post found (by rfl)
      first
      | exact loadResult _ _
      | exact loadLowAgain _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, cil_guard, observerCount, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.binary,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists post found (by rfl)
    · simpa only [← flag] using storeCarry
    exact done

#print axioms scalar_next_product
#print axioms scalar_accumulate
end UInt256Proof.Multiply.ScalarSafety

namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

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
theorem scalar_products (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [input] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [input] [output] frame (scalarProducts original input word) →
      ∃ fuel final returned,
        run program fuel methodIndex 66 (scalarArgs input word output) frame
          [.scalar (.i64 (inputLimb original input 3))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex 22 (scalarArgs input word output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply scalar_inputs profile program methodIndex wordIndex storageIndex found original entered current input output word frame originalCall enteredWF homes state post
  intro prepared preparedState
  apply scalar_first_product profile program methodIndex wordIndex storageIndex found contract original entered prepared input output word frame
    originalCall enteredWF homes preparedState post
  intro first firstState
  apply scalar_next_product profile program methodIndex wordIndex storageIndex found false contract original entered first input output word (inputLimb original input 1)
    frame _ _ originalCall enteredWF homes firstState (by simp [ladderInput, scalarFirstProduct, scalarInputs, rememberWord]) post
  intro second secondState
  apply scalar_accumulate profile program methodIndex wordIndex storageIndex found false original entered second input output word
    (lowProduct word (inputLimb original input 1)) (highProduct word (inputLimb original input 1))
    (highProduct word (inputLimb original input 0)) frame _ _ enteredWF homes secondState
    (by simp [rememberWord]) (by simp [rememberWord, scalarFirstProduct]) post
  intro summed summedState
  apply scalar_next_product profile program methodIndex wordIndex storageIndex found true contract original entered summed input output word (inputLimb original input 2)
    frame _ _ originalCall enteredWF homes summedState
    (by simp [ladderInput, ladderResult, scalarFirstProduct, scalarInputs, rememberWord]) post
  intro third thirdState
  apply scalar_accumulate profile program methodIndex wordIndex storageIndex found true original entered third input output word
    (lowProduct word (inputLimb original input 2)) (highProduct word (inputLimb original input 2))
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))
    frame _ _ enteredWF homes thirdState (by simp [rememberWord])
    (by simp [rememberWord, scalarCarry]) post
  exact continuation

#print axioms scalar_products
end UInt256Proof.Multiply.ScalarSafety

namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

abbrev ScalarResult (original final : Memory) (input output : Reference)
    (word : BitVec 64) (returned : List Value) : Prop :=
  OutputResult original final output (inputValue original input * BitVec.ofNat 256 word.toNat) returned

theorem scalar_output_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (original entered current : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [input] [output] frame
      (scalarProducts original input word)) :
    ∃ fuel final returned,
      run program fuel methodIndex 66 (scalarArgs input word output) frame
        [.scalar (.i64 (inputLimb original input 3))] current = .ok (final, returned) ∧
      ScalarResult original final input output word returned := by
  let words := scalarLimbs (inputLimb original input) word
  let carry := scalarCarry word (inputLimb original input 2)
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))
  let post := fun final returned => ScalarResult original final input output word returned
  have loadCarry := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (scalarBody profile wordIndex storageIndex)) (args := scalarArgs input word output) (pc := pc) (stack := stack)
    (index := 3) carry (by simp [scalarProducts, ladderWords, rememberWord, carry, scalarCarry])
  obtain ⟨prepared, storedLast, preparedState⟩ := state.store enteredWF homes 8 (by rfl) (words 3)
    70 (scalarArgs input word output) [] (body := (scalarBody profile wordIndex storageIndex))
  have lastValue : words 3 = inputLimb original input 3 * word + carry := by
    simp [words, scalarLimbs, CIL.fin_val_three, lowProduct, carry, BitVec.mul_comm]
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 4
    apply run_next_exists post found (by rfl)
    first
    | exact loadCarry _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, cil_guard, observerCount, scalarArgs, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simpa only [lastValue] using storedLast
  have formed := preparedState.call.output_formed (by simp : output ∈ [output])
  have load (index : Fin 4) (pc : Nat) (stack : List Value) :
      step (scalarBody profile wordIndex storageIndex) (.local (if index = 0 then 4 else 5 + index.val)) pc
        (scalarArgs input word output) frame stack prepared =
        .ok (.next (pc + 1) (.scalar (.i64 (words index)) :: stack) frame prepared) := by
    apply preparedState.snapshots.load
    obtain ⟨i, bound⟩ := index
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [words, scalarLimbs, scalarProducts, ladderWords, scalarFirstProduct,
        rememberWord, scalarCarry]
  iterate 5
    apply run_next_exists post found (by rfl)
    first
    | exact load 0 _ _
    | exact load 1 _ _
    | exact load 2 _ _
    | exact load 3 _ _
    | simp [step, cil_guard, observerCount, scalarArgs, checkedValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    storage prepared [input] output (words 0) (words 1) (words 2) (words 3) preparedState.call
  have stepped : step (scalarBody profile wordIndex storageIndex) (.call storageIndex 5) 76 (scalarArgs input word output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] prepared =
      .ok (.call storageIndex
        [.reference (.address output), .scalar (.i64 (words 0)), .scalar (.i64 (words 1)), .scalar (.i64 (words 2)),
          .scalar (.i64 (words 3))] [] prepared) := by
    simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run program 1 methodIndex 77 (scalarArgs input word output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : (scalarBody profile wordIndex storageIndex).code[77]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have mathematical := scalar_limbs_correct (inputLimb original input) word
  rw [input_limbs_value] at mathematical
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original prepared result [input] output _ frame
    originalCall valid owned preparedState.caller (packed.trans mathematical) readable outside⟩

theorem scalar_output (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (limbIndex : Nat) (scalar : profile.vector256Accelerated = false)
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile))
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (original entered current : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [input] [output] frame
      (scalarProducts original input word)) :
    ∃ fuel final returned,
      run program fuel methodIndex 66 (scalarArgs input word output) frame
        [.scalar (.i64 (inputLimb original input 3))] current = .ok (final, returned) ∧
      ScalarResult original final input output word returned :=
  scalar_output_with_storage profile program methodIndex wordIndex storageIndex (ProductStorage.scalar_contract profile scalar program storageIndex limbIndex storageFound limbsFound) found original entered current input output word frame originalCall enteredWF homes owned state
#print axioms scalar_output
end UInt256Proof.Multiply.ScalarSafety
namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem scalar_zero_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (original entered current : Memory) (input output : Reference)
    (frame : Frame) (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions program original [input] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [input] [output] frame known) :
    ∃ fuel final returned,
      run program fuel methodIndex 6 (scalarArgs input 0 output) frame [] current =
        .ok (final, returned) ∧ ScalarResult original final input output 0 returned := by
  let post := fun final returned => ScalarResult original final input output 0 returned
  have formed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 9
    apply run_next_exists post found (by rfl)
    simp [step, cil_guard, observerCount, scalarArgs, checkedValue, numericValue, formValue, formed, checkedAt,
      pureArity, scalars, CIL.step.eq_def, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    storage current [input] output 0 0 0 0 state.call
  have stepped : step (scalarBody profile wordIndex storageIndex) (.call storageIndex 5) 15 (scalarArgs input 0 output) frame
      [.scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0),
        .reference (.address output)] current =
      .ok (.call storageIndex [.reference (.address output), .scalar (.i64 0),
        .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0)] [] current) := by
    simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run program 1 methodIndex 16 (scalarArgs input 0 output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : (scalarBody profile wordIndex storageIndex).code[16]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  refine ⟨fuel, leaveFrame frame result, [], ran,
    output_result_of_storage original current result [input] output _ frame originalCall valid owned
      state.caller ?_ readable outside⟩
  simpa using value

theorem scalar_zero (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex limbIndex : Nat)
    (scalar : profile.vector256Accelerated = false)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex))
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile)) (original entered current : Memory) (input output : Reference)
    (frame : Frame) (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions program original [input] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [input] [output] frame known) :
    ∃ fuel final returned,
      run program fuel methodIndex 6 (scalarArgs input 0 output) frame [] current =
        .ok (final, returned) ∧ ScalarResult original final input output 0 returned :=
  scalar_zero_with_storage profile program methodIndex wordIndex storageIndex (ProductStorage.scalar_contract profile scalar program storageIndex limbIndex storageFound limbsFound) found original entered current input output frame known originalCall owned state
theorem scalar_one_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (_storage : ProductStorage.Contract program storageIndex)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (original entered current : Memory) (input output : Reference)
    (frame : Frame) (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions program original [input] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [input] [output] frame known) :
    ∃ fuel final returned,
      run program fuel methodIndex 17 (scalarArgs input 1 output) frame [] current =
        .ok (final, returned) ∧ ScalarResult original final input output 1 returned := by
  let bits := inputValue current input
  have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨result, written, valid, outside, readback⟩ := state.call.write_output_slice
    (by simp : output ∈ [output]) 0 (numberBytes bits.toNat 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  change write current output (numberBytes bits.toNat 32) 1 = .ok result at written
  simp only [bits] at written length
  have loaded := input_encoded program current [input] [output] state.call input (by simp)
  have inputFormed := state.call.input_formed (by simp : input ∈ [input])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  let post := fun final returned => ScalarResult original final input output 1 returned
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 4
    apply run_next_exists post found (by rfl)
    · simp [step, cil_guard, observerCount, scalarArgs, checkedValue, formValue, inputFormed, outputFormed, checkedAt,
      pureArity, instruction, dereference, ordinaryAccessAlignment, loaded, referenceAt, written, length,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
      done
  have finished : run program 1 methodIndex 21 (scalarArgs input 1 output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : (scalarBody profile wordIndex storageIndex).code[21]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  refine ⟨1, leaveFrame frame result, [], finished,
    output_result_of_storage original current result [input] output _ frame originalCall valid owned
      state.caller ?_ ⟨_, readback⟩ outside⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (originalCall.input_formed (by simp : input ∈ [input]))
  have bound := (originalCall.1.1.1 _ _ present).1
  have same : inputValue current input = inputValue original input := by
    unfold inputValue
    congr 1
    funext offset
    rw [state.caller input.allocation bound offset]
  simpa using
    (inputValue_of_encoded_read readback).trans same

#print axioms scalar_zero_with_storage
theorem scalar_one (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex limbIndex : Nat)
    (_scalar : profile.vector256Accelerated = false)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex))
    (_storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (_limbsFound : program[limbIndex]? = some (LimbStorage.body profile)) (original entered current : Memory) (input output : Reference)
    (frame : Frame) (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions program original [input] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [input] [output] frame known) :
    ∃ fuel final returned,
      run program fuel methodIndex 17 (scalarArgs input 1 output) frame [] current =
        .ok (final, returned) ∧ ScalarResult original final input output 1 returned :=
  scalar_one_with_storage profile program methodIndex wordIndex storageIndex (ProductStorage.scalar_contract profile _scalar program storageIndex limbIndex _storageFound _limbsFound) found original entered current input output frame known originalCall owned state
#print axioms scalar_one
end UInt256Proof.Multiply.ScalarSafety

namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem scalar_invoke_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (contract : WordContract program wordIndex) (memory : Memory) (input output : Reference)
    (word : BitVec 64) (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final,
      invoke program fuel methodIndex (scalarArgs input word output) memory = .ok (final, []) ∧
      ScalarResult memory final input output word [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := scalar_frame_setup profile program methodIndex wordIndex storageIndex found memory input output word call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ScalarResult memory final input output word returned
  have started : ∃ fuel final returned,
      run program fuel methodIndex 0 (scalarArgs input word output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    cil_contract_steps 3 [scalarArgs]
    by_cases large : 1 < word.toNat
    · have greater : BitVec.ofNat 64 1 < word := large
      cil_contract_steps 1 [greater]
      apply scalar_products profile program methodIndex wordIndex storageIndex found contract memory entered entered input output word frame call enteredWF homes state post
      intro current currentState
      exact scalar_output_with_storage profile program methodIndex wordIndex storageIndex storage found memory entered current input output word frame call enteredWF homes owned currentState
    · have unit : word = 0 ∨ word = 1 := by
        have cases : word.toNat = 0 ∨ word.toNat = 1 := by omega
        rcases cases with zero | one
        · left; exact BitVec.eq_of_toNat_eq zero
        · right; exact BitVec.eq_of_toNat_eq one
      rcases unit with rfl | rfl
      all_goals
        cil_contract_steps 3 [scalarArgs]
      · exact scalar_zero_with_storage profile program methodIndex wordIndex storageIndex storage found memory entered entered input output frame _ call owned state
      · exact scalar_one_with_storage profile program methodIndex wordIndex storageIndex storage found memory entered entered input output frame _ call owned state
  obtain ⟨fuel, final, returned, ran, result⟩ := started
  have returns := result.returns
  subst returned
  have inputFormed := call.input_formed (by simp : input ∈ [input])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (scalarArgs input word output).mapM (checkedValue memory) = .ok (scalarArgs input word output) := by
    simp [scalarArgs, checkedValue, numericValue, formValue, inputFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  exact invoke_of_run found checked setup ran

theorem scalar_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex limbIndex : Nat)
    (scalar : profile.vector256Accelerated = false)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex))
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile)) (contract : WordContract program wordIndex) (memory : Memory) (input output : Reference)
    (word : BitVec 64) (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final,
      invoke program fuel methodIndex (scalarArgs input word output) memory = .ok (final, []) ∧
      ScalarResult memory final input output word [] :=
  scalar_invoke_with_storage profile program methodIndex wordIndex storageIndex (ProductStorage.scalar_contract profile scalar program storageIndex limbIndex storageFound limbsFound) found contract memory input output word call
#print axioms scalar_invoke
end UInt256Proof.Multiply.ScalarSafety
