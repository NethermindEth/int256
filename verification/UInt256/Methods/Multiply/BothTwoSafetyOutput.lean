import UInt256.Methods.Multiply.BothTwoSafetyColumns
import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ZeroProducts
import UInt256.Safety.HalfRepresentation
import UInt256.Methods.Multiply.StorageSafety
import UInt256.Safety.OutputReturn

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def bothTwoFinalWords (original : Memory) (left right : Reference) :=
  let known := bothTwoSecondColumn original left right
  let reset := rememberWord (rememberWord known 11 (localWord known 7)) 7 0
  countWords (widenWords (countWords (countWords reset 11 5 7 11) 11 9 7 11) 1 2 13 12) 11 13 7 11

theorem both_two_final_column (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity bothTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (bothTwoSecondColumn original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (bothTwoFinalWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel bothTwoIndex 63 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 38 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  let known := bothTwoSecondColumn original left right
  apply run_next_exists post found (by rfl)
    (state.snapshots.load (localWord known 7) (by rfl))
  obtain ⟨copied, copiedStep, copiedState⟩ := state.store enteredWF homes 11 (by rfl) (localWord known 7)
    39 (productArgs left right output) [] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) copiedStep
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, CIL.step, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, resetStep, state0⟩ := copiedState.store enteredWF homes 7 (by rfl) 0
    42 (productArgs left right output) [] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) resetStep
  let k0 := rememberWord (rememberWord known 11 (localWord known 7)) 7 0
  apply run_local_word_call state0 originalCall enteredWF homes 11 5 7 11
    (localWord k0 11) (localWord k0 5) (countCarry (localWord k0 11) (localWord k0 5) 0)
    (localWord k0 11 + localWord k0 5) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state0.snapshots state0.call.1.1 7 _ _ 0 (by rfl)) post
  intro m1 state1
  let k1 := countWords k0 11 5 7 11
  apply run_local_word_call state1 originalCall enteredWF homes 11 9 7 11
    (localWord k1 11) (localWord k1 9) (countCarry (localWord k1 11) (localWord k1 9) (localWord k1 7))
    (localWord k1 11 + localWord k1 9) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 7 _ _ (localWord k1 7) (by rfl)) post
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
    (counting_local_effect state3.snapshots state3.call.1.1 7 _ _ (localWord k3 7) (by rfl)) post
  exact continuation

#print axioms both_two_final_column
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

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
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def ProductResult (original final : Memory) (left right output : Reference) (returned : List Value) :=
  OutputResult original final output (inputValue original left * inputValue original right) returned

theorem both_two_output (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (bothTwoFinalWords original left right))
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0)
    (rightUpper : inputLimb original right 2 = 0 ∧ inputLimb original right 3 = 0) :
    ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 63 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let known := bothTwoFinalWords original left right
  let words := bothTwoResultWords original left right
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have load (index : Nat) (value : BitVec 64) (present : known index = some value) (pc : Nat) (stack : List Value) :=
    state.snapshots.load (body := bothTwoBody) (args := productArgs left right output)
      (pc := pc) (stack := stack) (index := index) value present
  change ∃ fuel final returned, _ ∧ post final returned
  apply run_next_exists post found (by rfl)
  · simp [step, productArgs, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (load 4 (words 0) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 8 (words 1) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 11 (words 2) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 12 (localWord known 12) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 7 (localWord known 7) (by rfl) _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step bothTwoBody (.call productStoreIndex 5) 70 (productArgs left right output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] current =
      .ok (.call productStoreIndex [.reference (.address output), .scalar (.i64 (words 0)),
        .scalar (.i64 (words 1)), .scalar (.i64 (words 2)), .scalar (.i64 (words 3))] [] current) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run Extracted.program 1 bothTwoIndex 71 (productArgs left right output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : bothTwoBody.code[71]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original current result [left, right]
    output _ frame originalCall valid owned state.caller
    (packed.trans (both_two_words_correct original left right leftUpper rightUpper)) readable outside⟩

#print axioms both_two_output
end UInt256Proof.Multiply.Safety
