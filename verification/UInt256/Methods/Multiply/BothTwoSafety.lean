import UInt256.Generated.MethodTemplates
import CIL.Safety.Equations
import CIL.Safety.LocalSnapshotSteps
import UInt256.Methods.Multiply.LocalArithmeticSafety
import UInt256.Methods.Multiply.ProductStorage
import UInt256.Safety.PrivateInputValues
import UInt256.Safety.InputLocalSafety

/-! Checked multiplication of two two-limb operands, composed as one path over private homes. -/

namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

def bothTwoBody (profile : CIL.FeatureProfile) (wordIndex countIndex storageIndex : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method18 $(Lean.mkIdent `profile) $(Lean.mkIdent `countIndex) $(Lean.mkIdent `wordIndex) $(Lean.mkIdent `storageIndex))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)
def productArgs (left right output : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output)]

theorem both_two_frame_setup (profile : CIL.FeatureProfile) (program : CIL.Program) (index wordIndex countIndex storageIndex : Nat)
    (_found : program[index]? = some (bothTwoBody profile wordIndex countIndex storageIndex)) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame (bothTwoBody profile wordIndex countIndex storageIndex) (productArgs left right output) memory = .ok (frame, entered) ∧
      CompleteWritableHomes entered memory.nextIdentity (bothTwoBody profile wordIndex countIndex storageIndex).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : (bothTwoBody profile wordIndex countIndex storageIndex).localKinds = List.replicate 14 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (bothTwoBody profile wordIndex countIndex storageIndex)
    (by rfl) (by simp [kinds]) (by simp [kinds]) (by simp [kinds])
    (by simp [kinds]) (by simp [kinds]) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def bothTwoInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original right 0)) 1 (inputLimb original left 1)) 2 (inputLimb original right 1)


def bothTwoFirstProducts (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (bothTwoInputs original left right)
    4 (lowProduct (inputLimb original left 0) (inputLimb original right 0)))
    3 (highProduct (inputLimb original left 0) (inputLimb original right 0)))
    6 (lowProduct (inputLimb original left 0) (inputLimb original right 1)))
    5 (highProduct (inputLimb original left 0) (inputLimb original right 1))

def bothTwoSecondColumn (original : Memory) (left right : Reference) :=
  countWords (widenWords (countWords (rememberWord (bothTwoFirstProducts original left right) 7 0)
    3 6 7 8) 1 0 10 9) 8 10 7 8

def bothTwoFinalWords (original : Memory) (left right : Reference) :=
  let known := bothTwoSecondColumn original left right
  let reset := rememberWord (rememberWord known 11 (localWord known 7)) 7 0
  countWords (widenWords (countWords (countWords reset 11 5 7 11) 11 9 7 11) 1 2 13 12) 11 13 7 11

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


def ProductResult (original final : Memory) (left right output : Reference) (returned : List Value) :=
  OutputResult original final output (inputValue original left * inputValue original right) returned


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
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := both_two_frame_setup profile program
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
    apply run_input_to_local (argument := 1) (target := 0) state call enteredWF homes right
      (by simp) 0 (by rfl) (by rfl) found (by rfl) post
    intro m0 state0
    apply run_input_to_local (argument := 0) (target := 1) state0 call enteredWF homes left
      (by simp) 1 (by rfl) (by rfl) found (by rfl) post
    intro m1 state1
    apply run_input_to_local (argument := 1) (target := 2) state1 call enteredWF homes right
      (by simp) 1 (by rfl) (by rfl) found (by rfl) post
    intro m2 state2
    apply WP.exists_execution
    apply WP.step found (by rfl) (by rfl)
    apply run_widen_operand contract state2 call enteredWF homes 0 4 3 _
      (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m3 state3
    apply run_widen_operand contract state3 call enteredWF homes 2 6 5 _
      (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m4 state4
    iterate 2 (apply WP.step found (by rfl); rfl)
    apply run_store_local state4 enteredWF homes 7 (by rfl) 0 found (by rfl)
    intro m5 state5
    apply run_count_locals countFound state5 call enteredWF homes 3 6 7 8
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m6 state6
    apply run_widen_locals contract state6 call enteredWF homes 1 0 10 9
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m7 state7
    apply run_count_locals countFound state7 call enteredWF homes 8 10 7 8
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m8 state8
    apply WP.step found (by rfl) (state8.snapshots.load _ (localWord_remembered (by rfl)))
    apply run_store_local state8 enteredWF homes 11 (by rfl) _ found (by rfl)
    intro m9 state9
    iterate 2 (apply WP.step found (by rfl); rfl)
    apply run_store_local state9 enteredWF homes 7 (by rfl) 0 found (by rfl)
    intro m10 state10
    apply run_count_locals countFound state10 call enteredWF homes 11 5 7 11
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m11 state11
    apply run_count_locals countFound state11 call enteredWF homes 11 9 7 11
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m12 state12
    apply run_widen_locals contract state12 call enteredWF homes 1 2 13 12
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m13 state13
    apply run_count_locals countFound state13 call enteredWF homes 11 13 7 11
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro m14 state14
    have formed := state14.call.output_formed (by simp : output ∈ [output])
    cil_contract_steps (snapshots := state14.snapshots.toLocalSnapshots) [productArgs, formed]
    apply WP.exists_execution
    exact run_product_storage storage state14 call owned (bothTwoResultWords memory left right)
      (both_two_words_correct memory left right leftUpper rightUpper) found (by rfl) (by rfl)
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
end UInt256Proof.Multiply.BothTwo