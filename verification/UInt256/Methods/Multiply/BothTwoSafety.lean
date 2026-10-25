import CIL.Safety.Equations
import UInt256.Methods.Multiply.LocalArithmeticSafety
import UInt256.Methods.Multiply.ProductStorage
import UInt256.Safety.PrivateInputValues
import UInt256.Safety.OutputReturn

namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety

def bothTwoBody (profile : CIL.FeatureProfile) (wordIndex countIndex storageIndex : Nat) : CIL.Method := { profile := profile, returnsValue := false, locals := [.unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .fieldAt 0 8,
  .setLocal 0,
  .arg 0,
  .fieldAt 8 8,
  .setLocal 1,
  .arg 1,
  .fieldAt 8 8,
  .setLocal 2,
  .dup,
  .local 0,
  .localAddr 4,
  .call wordIndex 3,
  .setLocal 3,
  .local 2,
  .localAddr 6,
  .call wordIndex 3,
  .setLocal 5,
  .const32 0,
  .convI8,
  .setLocal 7,
  .local 3,
  .local 6,
  .localAddr 7,
  .call countIndex 3,
  .setLocal 8,
  .local 1,
  .local 0,
  .localAddr 10,
  .call wordIndex 3,
  .setLocal 9,
  .local 8,
  .local 10,
  .localAddr 7,
  .call countIndex 3,
  .setLocal 8,
  .local 7,
  .setLocal 11,
  .const32 0,
  .convI8,
  .setLocal 7,
  .local 11,
  .local 5,
  .localAddr 7,
  .call countIndex 3,
  .setLocal 11,
  .local 11,
  .local 9,
  .localAddr 7,
  .call countIndex 3,
  .setLocal 11,
  .local 1,
  .local 2,
  .localAddr 13,
  .call wordIndex 3,
  .setLocal 12,
  .local 11,
  .local 13,
  .localAddr 7,
  .call countIndex 3,
  .setLocal 11,
  .arg 2,
  .local 4,
  .local 8,
  .local 11,
  .local 12,
  .local 7,
  .add,
  .call storageIndex 5,
  .ret] }
def productArgs (left right output : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output)]

theorem both_two_frame_setup (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (_found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex)) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame (bothTwoBody profile wordIndex countIndex storageIndex) (productArgs left right output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity (bothTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : (bothTwoBody profile wordIndex countIndex storageIndex).localKinds = List.replicate 14 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (bothTwoBody profile wordIndex countIndex storageIndex)
    (by rfl) (by simp [kinds]) (by simp [kinds]) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def bothTwoInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original right 0)) 1 (inputLimb original left 1)) 2 (inputLimb original right 1)

theorem both_two_inputs (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex)) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (bothTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (bothTwoInputs original left right) →
      ∃ fuel final returned,
        run program fuel index 11 (productArgs left right output) frame
          [.scalar (.i64 (inputLimb original left 0))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have formedRight := state.call.input_formed (by simp : right ∈ [left, right])
  have loadLeft :=  state.input_field originalCall left (by simp) 0
  have loadRight := state.input_field originalCall right (by simp) 0
  simp only [Fin.val_zero, Nat.mul_zero] at loadLeft loadRight
  iterate 4
    apply run_next_exists post found (by rfl)
    · simp [step, cil_guard, observerCount, pureArity, productArgs, checkedValue, formValue, formedLeft, formedRight,
      loadLeft, loadRight, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
      done
  obtain ⟨m0, store0, state0⟩ := state.store enteredWF homes 0 (by rfl) (inputLimb original right 0)
    4 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) store0
  have formedLeft := state0.call.input_formed (by simp : left ∈ [left, right])
  have loadLeft :=  state0.input_field originalCall left (by simp) 1
  simp only [Fin.val_one, Nat.mul_one] at *
  iterate 2
    apply run_next_exists post found (by rfl)
    · simp [step, cil_guard, observerCount, pureArity, productArgs, checkedValue, formValue, formedLeft, loadLeft,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
      done
  obtain ⟨m1, store1, state1⟩ := state0.store enteredWF homes 1 (by rfl) (inputLimb original left 1)
    7 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) store1
  have formedRight := state1.call.input_formed (by simp : right ∈ [left, right])
  have loadRight := state1.input_field originalCall right (by simp) 1
  simp only [Fin.val_one, Nat.mul_one] at *
  iterate 2
    apply run_next_exists post found (by rfl)
    · simp [step, cil_guard, observerCount, pureArity, productArgs, checkedValue, formValue, formedRight, loadRight,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
      done
  obtain ⟨m2, store2, state2⟩ := state1.store enteredWF homes 2 (by rfl) (inputLimb original right 1)
    10 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  exact run_next_exists post found (by rfl) store2 (continuation m2 state2)

#print axioms both_two_frame_setup
#print axioms both_two_inputs
end UInt256Proof.Multiply.BothTwo
namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def bothTwoFirstProducts (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (bothTwoInputs original left right)
    4 (lowProduct (inputLimb original left 0) (inputLimb original right 0)))
    3 (highProduct (inputLimb original left 0) (inputLimb original right 0)))
    6 (lowProduct (inputLimb original left 0) (inputLimb original right 1)))
    5 (highProduct (inputLimb original left 0) (inputLimb original right 1))

theorem both_two_first_products (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (bothTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (bothTwoInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (bothTwoFirstProducts original left right) →
      ∃ fuel final returned,
        run program fuel index 20 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 11 (productArgs left right output) frame
        [.scalar (.i64 (inputLimb original left 0))] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨low0, slot0, ready0, formed0⟩ := state.home enteredWF homes 4 (by rfl)
  have load0 := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (bothTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 0) (inputLimb original right 0) (by simp [bothTwoInputs, rememberWord])
  iterate 3
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | simp [step, cil_guard, observerCount, pureArity, instruction, localAddress, slot0, formValue, formed0, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state originalCall homes 4 low0
    (inputLimb original left 0) (inputLimb original right 0) slot0 ready0 post found (by rfl)
  · simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed0, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro m0 state0
  obtain ⟨m1, stored0, state1⟩ := state0.store enteredWF homes 3 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 0))
    15 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) stored0
  obtain ⟨low1, slot1, ready1, formed1⟩ := state1.home enteredWF homes 6 (by rfl)
  have load1 := fun (pc : Nat) (stack : List Value) => state1.snapshots.load
    (body := (bothTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 2) (inputLimb original right 1) (by simp [bothTwoInputs, rememberWord])
  iterate 2
    apply run_next_exists post found (by rfl)
    first
    | exact load1 _ _
    | simp [step, cil_guard, observerCount, localAddress, slot1, formValue, formed1, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_word_call contract state1 originalCall homes 6 low1
    (inputLimb original left 0) (inputLimb original right 1) slot1 ready1 post found (by rfl)
  · simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed1, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl⟩
  intro m2 state2
  obtain ⟨m3, stored1, state3⟩ := state2.store enteredWF homes 5 (by rfl)
    (highProduct (inputLimb original left 0) (inputLimb original right 1))
    19 (productArgs left right output) [] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  exact run_next_exists post found (by rfl) stored1 (continuation m3 state3)

#print axioms both_two_first_products
end UInt256Proof.Multiply.BothTwo
namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls
def bothTwoSecondColumn (original : Memory) (left right : Reference) :=
  countWords (widenWords (countWords (rememberWord (bothTwoFirstProducts original left right) 7 0)
    3 6 7 8) 1 0 10 9) 8 10 7 8

theorem both_two_second_column (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (countFound : program[countIndex]? = some (CountSafety.body profile))
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (bothTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (bothTwoFirstProducts original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (bothTwoSecondColumn original left right) →
      ∃ fuel final returned,
        run program fuel index 38 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 20 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  iterate 2
    apply run_next_exists post found (by rfl)
    rfl
  obtain ⟨m0, stored, state0⟩ := state.store enteredWF homes 7 (by rfl) 0
    22 (productArgs left right output) [] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) stored
  let k0 := rememberWord (bothTwoFirstProducts original left right) 7 0
  apply run_local_word_call state0 originalCall enteredWF homes 3 6 7 8
    (localWord k0 3) (localWord k0 6) (countCarry (localWord k0 3) (localWord k0 6) 0)
    (localWord k0 3 + localWord k0 6) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state0.snapshots state0.call.1.1 7 _ _ 0 (by rfl)) post
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
    (counting_local_effect profile program countIndex countFound state2.snapshots state2.call.1.1 7 _ _ (localWord k2 7) (by rfl)) post
  exact continuation

#print axioms both_two_second_column
end UInt256Proof.Multiply.BothTwo
namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def bothTwoFinalWords (original : Memory) (left right : Reference) :=
  let known := bothTwoSecondColumn original left right
  let reset := rememberWord (rememberWord known 11 (localWord known 7)) 7 0
  countWords (widenWords (countWords (countWords reset 11 5 7 11) 11 9 7 11) 1 2 13 12) 11 13 7 11

theorem both_two_final_column (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (CountSafety.body profile)) (contract : WordContract program wordIndex)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (bothTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (bothTwoSecondColumn original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (bothTwoFinalWords original left right) →
      ∃ fuel final returned,
        run program fuel index 63 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 38 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  let known := bothTwoSecondColumn original left right
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (localWord known 7) (by rfl))
  obtain ⟨copied, copiedStep, copiedState⟩ := state.store enteredWF homes 11 (by rfl) (localWord known 7)
    39 (productArgs left right output) [] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) copiedStep
  iterate 2
    apply run_next_exists post found (by rfl)
    rfl
  obtain ⟨m0, resetStep, state0⟩ := copiedState.store enteredWF homes 7 (by rfl) 0
    42 (productArgs left right output) [] (body := (bothTwoBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by rfl) resetStep
  let k0 := rememberWord (rememberWord known 11 (localWord known 7)) 7 0
  apply run_local_word_call state0 originalCall enteredWF homes 11 5 7 11
    (localWord k0 11) (localWord k0 5) (countCarry (localWord k0 11) (localWord k0 5) 0)
    (localWord k0 11 + localWord k0 5) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state0.snapshots state0.call.1.1 7 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 11 5 7 11
  apply run_local_word_call state1 originalCall enteredWF homes 11 9 7 11
    (localWord k1 11) (localWord k1 9) (countCarry (localWord k1 11) (localWord k1 9) (localWord k1 7))
    (localWord k1 11 + localWord k1 9) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state1.snapshots state1.call.1.1 7 _ _ (localWord k1 7) (by rfl)) post
  intro m2 state2
  let k2 := countWords k1 11 9 7 11
  apply run_local_word_call state2 originalCall enteredWF homes 1 2 13 12
    (localWord k2 1) (localWord k2 2) (lowProduct (localWord k2 1) (localWord k2 2))
    (highProduct (localWord k2 1) (localWord k2 2)) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract m2 _ _ state2.call.1.1 reference ready) post
  intro m3 state3
  let k3 := widenWords k2 1 2 13 12
  apply run_local_word_call state3 originalCall enteredWF homes 11 13 7 11
    (localWord k3 11) (localWord k3 13) (countCarry (localWord k3 11) (localWord k3 13) (localWord k3 7))
    (localWord k3 11 + localWord k3 13) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect profile program countIndex countFound state3.snapshots state3.call.1.1 7 _ _ (localWord k3 7) (by rfl)) post
  exact continuation

#print axioms both_two_final_column
end UInt256Proof.Multiply.BothTwo

namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def bothTwoResultWords (original : Memory) (left right : Reference) : UInt256Model.Limbs := fun index =>
  let known := bothTwoFinalWords original left right
  if index.val = 0 then localWord known 4 else
  if index.val = 1 then localWord known 8 else
  if index.val = 2 then localWord known 11 else localWord known 12 + localWord known 7

theorem both_two_words_correct (original : Memory) (left right : Reference)
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0)
    (rightUpper : inputLimb original right 2 = 0 ∧ inputLimb original right 3 = 0) :
    UInt256Model.value (bothTwoResultWords original left right) = inputValue original left * inputValue original right := by
  have words : bothTwoResultWords original left right = productLimbs (inputLimb original left) (inputLimb original right) := by
    funext ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases leftUpper with ⟨left2, left3⟩
    rcases rightUpper with ⟨right2, right3⟩
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [bothTwoResultWords, bothTwoFinalWords, bothTwoSecondColumn, bothTwoFirstProducts,
        bothTwoInputs, localWord, widenWords, countWords, rememberWord,
        productLimbs, firstColumn, secondColumn, topWords, column, columnStep,
        left2, left3, right2, right3, countCarry, BitVec.add_assoc]
  rw [words, product_limbs_correct, input_limbs_value, input_limbs_value]

#print axioms both_two_words_correct
end UInt256Proof.Multiply.BothTwo

namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def ProductResult (original final : Memory) (left right output : Reference) (returned : List Value) :=
  OutputResult original final output (inputValue original left * inputValue original right) returned

theorem both_two_output_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex)) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (bothTwoFinalWords original left right))
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0)
    (rightUpper : inputLimb original right 2 = 0 ∧ inputLimb original right 3 = 0) :
    ∃ fuel final returned,
      run program fuel index 63 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let known := bothTwoFinalWords original left right
  let words := bothTwoResultWords original left right
  let post := fun final returned => ProductResult original final left right output returned
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have load (index : Nat) (value : BitVec 64) (present : known index = some value) (pc : Nat) (stack : List Value) :=
    state.snapshots.load (body := (bothTwoBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output)
      (pc := pc) (stack := stack) (index := index) value present
  change ∃ fuel final returned, _ ∧ post final returned
  apply run_next_exists post found (by rfl)
  · simp [step, cil_guard, observerCount, productArgs, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (load 4 (words 0) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 8 (words 1) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 11 (words 2) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 12 (localWord known 12) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 7 (localWord known 7) (by rfl) _ _)
  apply run_next_exists post found (by rfl)
  · rfl
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    storage current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step (bothTwoBody profile wordIndex countIndex storageIndex) (.call storageIndex 5) 70 (productArgs left right output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] current =
      .ok (.call storageIndex [.reference (.address output), .scalar (.i64 (words 0)),
        .scalar (.i64 (words 1)), .scalar (.i64 (words 2)), .scalar (.i64 (words 3))] [] current) := by
    simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run program 1 index 71 (productArgs left right output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : (bothTwoBody profile wordIndex countIndex storageIndex).code[71]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original current result [left, right]
    output _ frame originalCall valid owned state.caller
    (packed.trans (both_two_words_correct original left right leftUpper rightUpper)) readable outside⟩

theorem both_two_output (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex limbIndex : Nat)
    (scalar : profile.vector256Accelerated = false)
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex))
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile)) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (bothTwoFinalWords original left right))
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0)
    (rightUpper : inputLimb original right 2 = 0 ∧ inputLimb original right 3 = 0) :
    ∃ fuel final returned,
      run program fuel index 63 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned :=
  both_two_output_with_storage profile program index wordIndex countIndex storageIndex (ProductStorage.scalar_contract profile scalar program storageIndex limbIndex storageFound limbsFound) found original entered current left right output frame originalCall owned state leftUpper rightUpper
#print axioms both_two_output
end UInt256Proof.Multiply.BothTwo
namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem both_two_invoke_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (CountSafety.body profile)) (contract : WordContract program wordIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output])
    (leftUpper : inputLimb memory left 2 = 0 ∧ inputLimb memory left 3 = 0)
    (rightUpper : inputLimb memory right 2 = 0 ∧ inputLimb memory right 3 = 0) :
    ∃ fuel final,
      invoke program fuel index (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := both_two_frame_setup profile program index wordIndex countIndex storageIndex found memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run program fuel index 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply both_two_inputs profile program index wordIndex countIndex storageIndex found memory entered entered left right output frame call enteredWF homes state post
    intro m0 state0
    apply both_two_first_products profile program index wordIndex countIndex storageIndex found contract memory entered m0 left right output frame call enteredWF homes state0 post
    intro m1 state1
    apply both_two_second_column profile program index wordIndex countIndex storageIndex countFound found contract memory entered m1 left right output frame call enteredWF homes state1 post
    intro m2 state2
    apply both_two_final_column profile program index wordIndex countIndex storageIndex found countFound contract memory entered m2 left right output frame call enteredWF homes state2 post
    intro m3 state3
    exact both_two_output_with_storage profile program index wordIndex countIndex storageIndex storage found memory entered m3 left right output frame call owned state3 leftUpper rightUpper
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

theorem both_two_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex limbIndex : Nat)
    (scalar : profile.vector256Accelerated = false)
    (found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (CountSafety.body profile))
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile)) (contract : WordContract program wordIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output])
    (leftUpper : inputLimb memory left 2 = 0 ∧ inputLimb memory left 3 = 0)
    (rightUpper : inputLimb memory right 2 = 0 ∧ inputLimb memory right 3 = 0) :
    ∃ fuel final,
      invoke program fuel index (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  both_two_invoke_with_storage profile program index wordIndex countIndex storageIndex (ProductStorage.scalar_contract profile scalar program storageIndex limbIndex storageFound limbsFound) found countFound contract memory left right output call leftUpper rightUpper
#print axioms both_two_invoke
end UInt256Proof.Multiply.BothTwo
