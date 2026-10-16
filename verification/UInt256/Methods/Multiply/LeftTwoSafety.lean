import UInt256.Methods.Multiply.LocalArithmeticSafety
import UInt256.Methods.Multiply.ProductStorage
import UInt256.Safety.PrivateInputValues
import UInt256.Safety.OutputReturn
import UInt256.Safety.InputLocalSafety

namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety

def leftTwoBody (profile : CIL.FeatureProfile) (wordIndex countIndex storageIndex : Nat) : CIL.Method := { profile := profile, returnsValue := false, locals := [.unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .arg 0,
  .fieldAt 8 8,
  .setLocal 0,
  .arg 1,
  .fieldAt 0 8,
  .setLocal 1,
  .arg 1,
  .fieldAt 8 8,
  .setLocal 2,
  .arg 1,
  .fieldAt 16 8,
  .setLocal 3,
  .dup,
  .arg 1,
  .fieldAt 24 8,
  .mul,
  .local 0,
  .local 3,
  .mul,
  .add,
  .setLocal 4,
  .dup,
  .local 1,
  .localAddr 6,
  .call wordIndex 3,
  .setLocal 5,
  .dup,
  .local 2,
  .localAddr 8,
  .call wordIndex 3,
  .setLocal 7,
  .const32 0,
  .convI8,
  .setLocal 9,
  .local 5,
  .local 8,
  .localAddr 9,
  .call countIndex 3,
  .setLocal 10,
  .local 0,
  .local 1,
  .localAddr 12,
  .call wordIndex 3,
  .setLocal 11,
  .local 10,
  .local 12,
  .localAddr 9,
  .call countIndex 3,
  .setLocal 10,
  .local 9,
  .setLocal 13,
  .const32 0,
  .convI8,
  .setLocal 9,
  .local 13,
  .local 7,
  .localAddr 9,
  .call countIndex 3,
  .setLocal 13,
  .local 13,
  .local 11,
  .localAddr 9,
  .call countIndex 3,
  .setLocal 13,
  .local 3,
  .localAddr 15,
  .call wordIndex 3,
  .setLocal 14,
  .local 13,
  .local 15,
  .localAddr 9,
  .call countIndex 3,
  .setLocal 13,
  .local 4,
  .local 14,
  .add,
  .setLocal 4,
  .local 0,
  .local 2,
  .localAddr 17,
  .call wordIndex 3,
  .setLocal 16,
  .local 13,
  .local 17,
  .localAddr 9,
  .call countIndex 3,
  .setLocal 13,
  .local 4,
  .local 16,
  .local 9,
  .add,
  .add,
  .setLocal 4,
  .arg 2,
  .local 6,
  .local 10,
  .local 13,
  .local 4,
  .call storageIndex 5,
  .ret] }

def productArgs (left right output : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output)]

theorem left_two_frame_setup (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (_found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex)) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame (leftTwoBody profile wordIndex countIndex storageIndex) (productArgs left right output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : (leftTwoBody profile wordIndex countIndex storageIndex).localKinds = List.replicate 18 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (leftTwoBody profile wordIndex countIndex storageIndex)
    (by rfl) (by simp [kinds]) (by rfl) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def leftTwoInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original left 1)) 1 (inputLimb original right 0))
    2 (inputLimb original right 1)) 3 (inputLimb original right 2)

theorem left_two_inputs (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex)) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (leftTwoInputs original left right) →
      ∃ fuel final returned,
        run program fuel index 14 (productArgs left right output) frame
          [.scalar (.i64 (inputLimb original left 0))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have formed := state.call.input_formed (by simp : left ∈ [left, right])
  have reading := state.input_field originalCall left (by simp) 0
  simp only [Fin.val_zero, Nat.mul_zero] at reading
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, productArgs, checkedValue, formValue, formed, reading, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_input_to_local (argument := 0) (target := 0) state originalCall enteredWF homes left (by simp) 1
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m0 state0
  apply run_input_to_local (argument := 1) (target := 1) state0 originalCall enteredWF homes right (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m1 state1
  apply run_input_to_local (argument := 1) (target := 2) state1 originalCall enteredWF homes right (by simp) 1
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m2 state2
  apply run_input_to_local (argument := 1) (target := 3) state2 originalCall enteredWF homes right (by simp) 2
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  exact continuation

#print axioms left_two_frame_setup
#print axioms left_two_inputs
end UInt256Proof.Multiply.LeftTwo


namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety

def leftTwoTop (original : Memory) (left right : Reference) :=
  inputLimb original left 0 * inputLimb original right 3 + inputLimb original left 1 * inputLimb original right 2

theorem left_two_top (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex)) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (leftTwoInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (rememberWord (leftTwoInputs original left right) 4 (leftTwoTop original left right)) →
      ∃ fuel final returned,
        run program fuel index 23 (productArgs left right output) frame
          [.scalar (.i64 (inputLimb original left 0))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 14 (productArgs left right output) frame
        [.scalar (.i64 (inputLimb original left 0))] current = .ok (final, returned) ∧ post final returned := by
  have formed := state.call.input_formed (by simp : right ∈ [left, right])
  have reading := state.input_field originalCall right (by simp) 3
  simp only [CIL.fin_val_three, Nat.reduceMul] at reading
  have load0 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (leftTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 0) (inputLimb original left 1) (by rfl)
  have load3 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (leftTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 3) (inputLimb original right 2) (by rfl)
  apply run_next_exists post found (by rfl) (by rfl)
  iterate 7
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | exact load3 _ _
    | simp [step, pureArity, productArgs, checkedValue, numericValue, formValue, formed,
        reading, checkedAt, scalars, CIL.step.eq_def, CIL.binary,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes 4 (by rfl) (leftTwoTop original left right)
    22 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms left_two_top
end UInt256Proof.Multiply.LeftTwo




namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def leftTwoFirstProducts (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (rememberWord (leftTwoInputs original left right) 4 (leftTwoTop original left right))
    6 (lowProduct (inputLimb original left 0) (inputLimb original right 0)))
    5 (highProduct (inputLimb original left 0) (inputLimb original right 0)))
    8 (lowProduct (inputLimb original left 0) (inputLimb original right 1)))
    7 (highProduct (inputLimb original left 0) (inputLimb original right 1))

theorem left_two_first_products (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (rememberWord (leftTwoInputs original left right) 4 (leftTwoTop original left right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (leftTwoFirstProducts original left right) →
      ∃ fuel final returned,
        run program fuel index 33 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 23 (productArgs left right output) frame
        [.scalar (.i64 (inputLimb original left 0))] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨low0, slot0, ready0, formed0⟩ := state.home enteredWF homes 6 (by rfl)
  have load0 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (leftTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 1) (inputLimb original right 0) (by simp [leftTwoInputs, rememberWord])
  iterate 3
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | simp [step, pureArity, instruction, localAddress, slot0, formValue, formed0, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state originalCall homes 6 low0
    (inputLimb original left 0) (inputLimb original right 0) slot0 ready0 post found (by rfl)
  · simp [step, checkedValue, numericValue, formValue, formed0, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro m0 state0
  obtain ⟨m1, stored0, state1⟩ := state0.store enteredWF homes 5 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 0))
    27 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) stored0
  obtain ⟨low1, slot1, ready1, formed1⟩ := state1.home enteredWF homes 8 (by rfl)
  have load1 := fun (pc : Nat) (stack : List Value) => state1.snapshots.load
    (body := (leftTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 2) (inputLimb original right 1) (by simp [leftTwoInputs, rememberWord])
  iterate 3
    apply run_next_exists post found (by rfl)
    first
    | exact load1 _ _
    | simp [step, pureArity, instruction, localAddress, slot1, formValue, formed1, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state1 originalCall homes 8 low1
    (inputLimb original left 0) (inputLimb original right 1) slot1 ready1 post found (by rfl)
  · simp [step, checkedValue, numericValue, formValue, formed1, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro m2 state2
  obtain ⟨m3, stored1, state3⟩ := state2.store enteredWF homes 7 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 1))
    32 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  exact run_next_exists post found (by rfl) stored1 (continuation m3 state3)

#print axioms left_two_first_products
end UInt256Proof.Multiply.LeftTwo



namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety
def localWord (known : Nat → Option (BitVec 64)) (index : Nat) : BitVec 64 := (known index).getD 0

def widenWords (known : Nat → Option (BitVec 64)) (left right target result : Nat) :=
  rememberWord (rememberWord known target (lowProduct (localWord known left) (localWord known right)))
    result (highProduct (localWord known left) (localWord known right))

def countWords (known : Nat → Option (BitVec 64)) (left right counter result : Nat) :=
  rememberWord (rememberWord known counter
    (countCarry (localWord known left) (localWord known right) (localWord known counter)))
    result (localWord known left + localWord known right)


end UInt256Proof.Multiply.LeftTwo


namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def leftTwoSecondColumn (original : Memory) (left right : Reference) :=
  countWords (widenWords (countWords (rememberWord (leftTwoFirstProducts original left right) 9 0)
    5 8 9 10) 0 1 12 11) 10 12 9 10

theorem left_two_second_column (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (UInt256Proof.Multiply.CountSafety.body profile)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (leftTwoFirstProducts original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (leftTwoSecondColumn original left right) →
      ∃ fuel final returned,
        run program fuel index 51 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 33 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] current =
        .ok (final, returned) ∧ post final returned := by
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step.eq_def, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, stored, state0⟩ := state.store enteredWF homes 9 (by rfl) 0
    35 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) stored
  let k0 := rememberWord (leftTwoFirstProducts original left right) 9 0
  apply run_local_word_call state0 originalCall enteredWF homes 5 8 9 10
    (localWord k0 5) (localWord k0 8) (countCarry (localWord k0 5) (localWord k0 8) 0)
    (localWord k0 5 + localWord k0 8) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state0.snapshots state0.call.1.1 9 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 5 8 9 10
  apply run_local_word_call state1 originalCall enteredWF homes 0 1 12 11
    (localWord k1 0) (localWord k1 1) (lowProduct (localWord k1 0) (localWord k1 1))
    (highProduct (localWord k1 0) (localWord k1 1)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract m1 _ _ state1.call.1.1 reference ready) post
  intro m2 state2
  let k2 := widenWords k1 0 1 12 11
  apply run_local_word_call state2 originalCall enteredWF homes 10 12 9 10
    (localWord k2 10) (localWord k2 12) (countCarry (localWord k2 10) (localWord k2 12) (localWord k2 9))
    (localWord k2 10 + localWord k2 12) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state2.snapshots state2.call.1.1 9 _ _ (localWord k2 9) (by rfl)) post
  exact continuation

#print axioms left_two_second_column
end UInt256Proof.Multiply.LeftTwo


namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def leftTwoMiddleWords (original : Memory) (left right : Reference) :=
  let known := leftTwoSecondColumn original left right
  let reset := rememberWord (rememberWord known 13 (localWord known 9)) 9 0
  countWords (countWords reset 13 7 9 13) 13 11 9 13

theorem left_two_middle_column (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (UInt256Proof.Multiply.CountSafety.body profile))
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (leftTwoSecondColumn original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (leftTwoMiddleWords original left right) →
      ∃ fuel final returned,
        run program fuel index 66 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 51 (productArgs left right output) frame [.scalar (.i64 (inputLimb original left 0))] current =
        .ok (final, returned) ∧ post final returned := by
  let known := leftTwoSecondColumn original left right
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (localWord known 9) (by rfl))
  obtain ⟨copied, copiedStep, copiedState⟩ := state.store enteredWF homes 13 (by rfl) (localWord known 9)
    52 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) copiedStep
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step.eq_def, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, resetStep, state0⟩ := copiedState.store enteredWF homes 9 (by rfl) 0
    55 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) resetStep
  let k0 := rememberWord (rememberWord known 13 (localWord known 9)) 9 0
  apply run_local_word_call state0 originalCall enteredWF homes 13 7 9 13
    (localWord k0 13) (localWord k0 7) (countCarry (localWord k0 13) (localWord k0 7) 0)
    (localWord k0 13 + localWord k0 7) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state0.snapshots state0.call.1.1 9 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 13 7 9 13
  apply run_local_word_call state1 originalCall enteredWF homes 13 11 9 13
    (localWord k1 13) (localWord k1 11) (countCarry (localWord k1 13) (localWord k1 11) (localWord k1 9))
    (localWord k1 13 + localWord k1 11) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state1.snapshots state1.call.1.1 9 _ _ (localWord k1 9) (by rfl)) post
  exact continuation

#print axioms left_two_middle_column
end UInt256Proof.Multiply.LeftTwo


namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def leftTwoUpperProduct (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (leftTwoMiddleWords original left right)
    15 (lowProduct (inputLimb original left 0) (inputLimb original right 2)))
    14 (highProduct (inputLimb original left 0) (inputLimb original right 2))

theorem left_two_upper_product (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (_countFound : program[countIndex]? = some (UInt256Proof.Multiply.CountSafety.body profile)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (leftTwoMiddleWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (leftTwoUpperProduct original left right) →
      ∃ fuel final returned,
        run program fuel index 70 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 66 (productArgs left right output) frame
        [.scalar (.i64 (inputLimb original left 0))] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, slot, ready, formed⟩ := state.home enteredWF homes 15 (by rfl)
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (inputLimb original right 2) (by rfl))
  apply run_next_exists post found (by rfl)
  · simp [step, localAddress, slot, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state originalCall homes 15 reference
    (inputLimb original left 0) (inputLimb original right 2) slot ready post found (by rfl)
  · simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro middle middleState
  obtain ⟨after, stored, next⟩ := middleState.store enteredWF homes 14 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 2))
    69 (productArgs left right output) [] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  exact run_next_exists post found (by rfl) stored (continuation after next)

def leftTwoUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (leftTwoUpperProduct original left right) 13 15 9 13
  rememberWord known 4 (localWord known 4 + localWord known 14)

theorem left_two_upper_accumulate (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (UInt256Proof.Multiply.CountSafety.body profile))
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (leftTwoUpperProduct original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (leftTwoUpperWords original left right) →
      ∃ fuel final returned,
        run program fuel index 79 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 70 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  let k0 := leftTwoUpperProduct original left right
  apply run_local_word_call state originalCall enteredWF homes 13 15 9 13
    (localWord k0 13) (localWord k0 15) (countCarry (localWord k0 13) (localWord k0 15) (localWord k0 9))
    (localWord k0 13 + localWord k0 15) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state.snapshots state.call.1.1 9 _ _ (localWord k0 9) (by rfl)) post
  intro middle middleState
  let k1 := countWords k0 13 15 9 13
  apply run_next_exists post found (by rfl) (middleState.snapshots.load (localWord k1 4) (by rfl))
  apply run_next_exists post found (by rfl) (middleState.snapshots.load (localWord k1 14) (by rfl))
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step.eq_def, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := middleState.store enteredWF homes 4 (by rfl)
    (localWord k1 4 + localWord k1 14) 78 (productArgs left right output) [] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms left_two_upper_product
#print axioms left_two_upper_accumulate
end UInt256Proof.Multiply.LeftTwo


namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def leftTwoFinalWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (leftTwoUpperWords original left right) 0 2 17 16) 13 17 9 13
  rememberWord known 4 (localWord known 4 + (localWord known 16 + localWord known 9))

theorem left_two_final (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (UInt256Proof.Multiply.CountSafety.body profile)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (leftTwoUpperWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (leftTwoFinalWords original left right) →
      ∃ fuel final returned,
        run program fuel index 95 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 79 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  let k0 := leftTwoUpperWords original left right
  apply run_local_word_call state originalCall enteredWF homes 0 2 17 16
    (localWord k0 0) (localWord k0 2) (lowProduct (localWord k0 0) (localWord k0 2))
    (highProduct (localWord k0 0) (localWord k0 2)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 0 2 17 16
  apply run_local_word_call state1 originalCall enteredWF homes 13 17 9 13
    (localWord k1 13) (localWord k1 17) (countCarry (localWord k1 13) (localWord k1 17) (localWord k1 9))
    (localWord k1 13 + localWord k1 17) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state1.snapshots state1.call.1.1 9 _ _ (localWord k1 9) (by rfl)) post
  intro m2 state2
  let k2 := countWords k1 13 17 9 13
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 4) (by rfl))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 16) (by rfl))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 9) (by rfl))
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, numericValue, CIL.step.eq_def, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 4 (by rfl)
    (localWord k2 4 + (localWord k2 16 + localWord k2 9)) 94 (productArgs left right output) [] (body := (leftTwoBody profile wordIndex countIndex storageIndex))
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms left_two_final
end UInt256Proof.Multiply.LeftTwo
namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety

def leftTwoResultWords (original : Memory) (left right : Reference) : UInt256Model.Limbs := fun index =>
  let known := leftTwoFinalWords original left right
  localWord known (if index.val = 0 then 6 else if index.val = 1 then 10 else if index.val = 2 then 13 else 4)

theorem left_two_words_correct (original : Memory) (left right : Reference)
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0) :
    UInt256Model.value (leftTwoResultWords original left right) = inputValue original left * inputValue original right := by
  have words : leftTwoResultWords original left right = productLimbs (inputLimb original left) (inputLimb original right) := by
    funext ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases leftUpper with ⟨left2, left3⟩
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [leftTwoResultWords, leftTwoFinalWords, leftTwoUpperWords, leftTwoUpperProduct, leftTwoMiddleWords,
        leftTwoSecondColumn, leftTwoFirstProducts, leftTwoInputs, leftTwoTop,
        localWord, widenWords, countWords, rememberWord,
        productLimbs, firstColumn, secondColumn, topWords, column, columnStep,
        left2, left3, countCarry, lowProduct, BitVec.add_assoc]
  rw [words, product_limbs_correct, input_limbs_value, input_limbs_value]

#print axioms left_two_words_correct
end UInt256Proof.Multiply.LeftTwo
namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def ProductResult (original final : Memory) (left right output : Reference) (returned : List Value) :=
  OutputResult original final output (inputValue original left * inputValue original right) returned

theorem left_two_output (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex limbIndex : Nat)
    (scalar : profile.vector256Accelerated = false)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile)) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (leftTwoFinalWords original left right))
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0)
 :
    ∃ fuel final returned,
      run program fuel index 95 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let known := leftTwoFinalWords original left right
  let words := leftTwoResultWords original left right
  let post := fun final returned => ProductResult original final left right output returned
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have load (index : Nat) (value : BitVec 64) (present : known index = some value) (pc : Nat) (stack : List Value) :=
    state.snapshots.load (body := (leftTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output)
      (pc := pc) (stack := stack) (index := index) value present
  change ∃ fuel final returned, _ ∧ post final returned
  apply run_next_exists post found (by rfl)
  · simp [step, productArgs, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (load 6 (words 0) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 10 (words 1) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 13 (words 2) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 4 (words 3) (by rfl) _ _)
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    ProductStorage.store_product_contract profile scalar program storageIndex limbIndex storageFound limbsFound current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step (leftTwoBody profile wordIndex countIndex storageIndex) (.call storageIndex 5) 100 (productArgs left right output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] current =
      .ok (.call storageIndex [.reference (.address output), .scalar (.i64 (words 0)),
        .scalar (.i64 (words 1)), .scalar (.i64 (words 2)), .scalar (.i64 (words 3))] [] current) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run program 1 index 101 (productArgs left right output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : (leftTwoBody profile wordIndex countIndex storageIndex).code[101]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original current result [left, right]
    output _ frame originalCall valid owned state.caller
    (packed.trans (left_two_words_correct original left right leftUpper)) readable outside⟩

#print axioms left_two_output
end UInt256Proof.Multiply.LeftTwo

namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem left_two_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex limbIndex : Nat)
    (scalar : profile.vector256Accelerated = false)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (CountSafety.body profile))
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile)) (contract : WordContract program wordIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output])
    (leftUpper : inputLimb memory left 2 = 0 ∧ inputLimb memory left 3 = 0)
 :
    ∃ fuel final,
      invoke program fuel index (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := left_two_frame_setup profile program index wordIndex countIndex storageIndex found memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run program fuel index 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply left_two_inputs profile program index wordIndex countIndex storageIndex found memory entered entered left right output frame call enteredWF homes state post
    intro m0 state0
    apply left_two_top profile program index wordIndex countIndex storageIndex found memory entered m0 left right output frame call enteredWF homes state0 post
    intro m1 state1
    apply left_two_first_products profile program index wordIndex countIndex storageIndex found contract memory entered m1 left right output frame call enteredWF homes state1 post
    intro m2 state2
    apply left_two_second_column profile program index wordIndex countIndex storageIndex found countFound contract memory entered m2 left right output frame call enteredWF homes state2 post
    intro m3 state3
    apply left_two_middle_column profile program index wordIndex countIndex storageIndex found countFound memory entered m3 left right output frame call enteredWF homes state3 post
    intro m4 state4
    apply left_two_upper_product profile program index wordIndex countIndex storageIndex found countFound contract memory entered m4 left right output frame call enteredWF homes state4 post
    intro m5 state5
    apply left_two_upper_accumulate profile program index wordIndex countIndex storageIndex found countFound memory entered m5 left right output frame call enteredWF homes state5 post
    intro m6 state6
    apply left_two_final profile program index wordIndex countIndex storageIndex found countFound contract memory entered m6 left right output frame call enteredWF homes state6 post
    intro m7 state7
    exact left_two_output profile program index wordIndex countIndex storageIndex limbIndex scalar found storageFound limbsFound memory entered m7 left right output frame call owned state7 leftUpper
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns := result.returns
  subst returned
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  exact invoke_of_run found checked setup ran

#print axioms left_two_invoke
end UInt256Proof.Multiply.LeftTwo
