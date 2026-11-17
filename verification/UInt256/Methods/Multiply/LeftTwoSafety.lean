import UInt256.Generated.MethodTemplates
import CIL.Safety.Equations
import CIL.Safety.LocalSnapshotSteps
import UInt256.Methods.Multiply.LocalArithmeticSafety
import UInt256.Methods.Multiply.ProductStorage
import UInt256.Safety.PrivateInputValues
import UInt256.Safety.InputLocalSafety

/-! Checked multiplication of a two-limb operand by a full operand, composed as one path
    over private homes. -/

namespace UInt256Proof.Multiply.LeftTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls
open UInt256Proof.Multiply.BothTwo (localWord widenWords countWords localWord_remembered
  run_store_local run_widen_operand run_widen_locals run_count_locals run_product_storage)

def leftTwoBody (profile : CIL.FeatureProfile) (wordIndex countIndex storageIndex : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method19 $(Lean.mkIdent `profile) $(Lean.mkIdent `countIndex) $(Lean.mkIdent `wordIndex) $(Lean.mkIdent `storageIndex))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

def productArgs (left right output : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output)]

theorem left_two_frame_setup (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (_found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex)) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame (leftTwoBody profile wordIndex countIndex storageIndex) (productArgs left right output) memory = .ok (frame, entered) ∧
      CompleteWritableHomes entered memory.nextIdentity (leftTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : (leftTwoBody profile wordIndex countIndex storageIndex).localKinds = List.replicate 18 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (leftTwoBody profile wordIndex countIndex storageIndex)
    (by rfl) (by simp [kinds]) (by simp [kinds]) (by simp [kinds])
    (by simp [kinds]) (by simp [kinds]) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def leftTwoInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original left 1)) 1 (inputLimb original right 0))
    2 (inputLimb original right 1)) 3 (inputLimb original right 2)

def leftTwoTop (original : Memory) (left right : Reference) :=
  inputLimb original left 0 * inputLimb original right 3 + inputLimb original left 1 * inputLimb original right 2

def leftTwoFirstProducts (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (rememberWord (leftTwoInputs original left right) 4 (leftTwoTop original left right))
    6 (lowProduct (inputLimb original left 0) (inputLimb original right 0)))
    5 (highProduct (inputLimb original left 0) (inputLimb original right 0)))
    8 (lowProduct (inputLimb original left 0) (inputLimb original right 1)))
    7 (highProduct (inputLimb original left 0) (inputLimb original right 1))

def leftTwoSecondColumn (original : Memory) (left right : Reference) :=
  countWords (widenWords (countWords (rememberWord (leftTwoFirstProducts original left right) 9 0)
    5 8 9 10) 0 1 12 11) 10 12 9 10

def leftTwoMiddleWords (original : Memory) (left right : Reference) :=
  let known := leftTwoSecondColumn original left right
  let reset := rememberWord (rememberWord known 13 (localWord known 9)) 9 0
  countWords (countWords reset 13 7 9 13) 13 11 9 13

def leftTwoUpperProduct (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (leftTwoMiddleWords original left right)
    15 (lowProduct (inputLimb original left 0) (inputLimb original right 2)))
    14 (highProduct (inputLimb original left 0) (inputLimb original right 2))

def leftTwoUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (leftTwoUpperProduct original left right) 13 15 9 13
  rememberWord known 4 (localWord known 4 + localWord known 14)

def leftTwoFinalWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (leftTwoUpperWords original left right) 0 2 17 16) 13 17 9 13
  rememberWord known 4 (localWord known 4 + (localWord known 16 + localWord known 9))

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

def ProductResult (original final : Memory) (left right output : Reference) (returned : List Value) :=
  OutputResult original final output (inputValue original left * inputValue original right) returned

theorem left_two_invoke_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[index]? = some (leftTwoBody profile wordIndex countIndex storageIndex))
    (countFound : program[countIndex]? = some (CountSafety.body profile)) (contract : WordContract program wordIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output])
    (leftUpper : inputLimb memory left 2 = 0 ∧ inputLimb memory left 3 = 0)
 :
    ∃ fuel final,
      invoke program fuel index (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := left_two_frame_setup profile program
    index wordIndex countIndex storageIndex found memory left right output call
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run program fuel index 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
    have readLeft := state.input_field call left (by simp) 0
    cil_contract_steps 2 [productArgs, formedLeft, readLeft]
    apply run_input_to_local (argument := 0) (target := 0) state call enteredWF homes left
      (by simp) 1 (by rfl) (by rfl) found (by rfl) post
    intro m0 state0
    apply run_input_to_local (argument := 1) (target := 1) state0 call enteredWF homes right
      (by simp) 0 (by rfl) (by rfl) found (by rfl) post
    intro m1 state1
    apply run_input_to_local (argument := 1) (target := 2) state1 call enteredWF homes right
      (by simp) 1 (by rfl) (by rfl) found (by rfl) post
    intro m2 state2
    apply run_input_to_local (argument := 1) (target := 3) state2 call enteredWF homes right
      (by simp) 2 (by rfl) (by rfl) found (by rfl) post
    intro m3 state3
    have formed := state3.call.1.1
    have retained := state3.authority
    have formedRight := state3.call.input_formed (by simp : right ∈ [left, right])
    have readRight := state3.input_field call right (by simp) 3
    cil_contract_steps (snapshots := state3.snapshots.toLocalSnapshots) 10
      [productArgs, formedRight, readRight]
    apply WP.exists_execution
    have state4 := state3.after_word_write homes (by assumption) localWrite
    apply run_widen_operand contract state4 call enteredWF homes 1 6 5 _
      (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m5 state5
    apply WP.step found (by rfl) (by rfl)
    apply run_widen_operand contract state5 call enteredWF homes 2 8 7 _
      (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m6 state6
    iterate 2 (apply WP.step found (by rfl); rfl)
    apply run_store_local state6 enteredWF homes 9 (by rfl) 0 found (by rfl)
    intro m7 state7
    apply run_count_locals countFound state7 call enteredWF homes 5 8 9 10
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m8 state8
    apply run_widen_locals contract state8 call enteredWF homes 0 1 12 11
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m9 state9
    apply run_count_locals countFound state9 call enteredWF homes 10 12 9 10
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m10 state10
    apply WP.step found (by rfl) (state10.snapshots.load _ (localWord_remembered (by rfl)))
    apply run_store_local state10 enteredWF homes 13 (by rfl) _ found (by rfl)
    intro m11 state11
    iterate 2 (apply WP.step found (by rfl); rfl)
    apply run_store_local state11 enteredWF homes 9 (by rfl) 0 found (by rfl)
    intro m12 state12
    apply run_count_locals countFound state12 call enteredWF homes 13 7 9 13
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m13 state13
    apply run_count_locals countFound state13 call enteredWF homes 13 11 9 13
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m14 state14
    apply run_widen_operand contract state14 call enteredWF homes 3 15 14 _
      (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m15 state15
    apply run_count_locals countFound state15 call enteredWF homes 13 15 9 13
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m16 state16
    cil_contract_steps (snapshots := state16.snapshots.toLocalSnapshots) []
    apply WP.exists_execution
    apply run_store_local state16 enteredWF homes 4 (by rfl) _ found (by rfl)
    intro m17 state17
    apply run_widen_locals contract state17 call enteredWF homes 0 2 17 16
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m18 state18
    apply run_count_locals countFound state18 call enteredWF homes 13 17 9 13
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m19 state19
    have formed := state19.call.1.1
    have retained := state19.authority
    have valid := state19.call.1
    cil_contract_steps (snapshots := state19.snapshots.toLocalSnapshots) [productArgs]
    apply WP.exists_execution
    exact run_product_storage storage (state19.after_word_write homes (by assumption) localWrite_1)
      call owned (leftTwoResultWords memory left right)
      (left_two_words_correct memory left right leftUpper) found (by rfl) (by rfl)
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
      ProductResult memory final left right output [] :=
  left_two_invoke_with_storage profile program index wordIndex countIndex storageIndex (ProductStorage.scalar_contract profile scalar program storageIndex limbIndex storageFound limbsFound) found countFound contract memory left right output call leftUpper
