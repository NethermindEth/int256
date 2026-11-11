import UInt256.Generated.MethodTemplates
import CIL.Safety.Equations
import CIL.Safety.LocalSnapshotSteps
import UInt256.Safety.PrivateInputValues
import UInt256.Safety.InputLocalSafety
import UInt256.Methods.Multiply.LocalArithmeticSafety
import UInt256.Methods.Multiply.ScalarValue
import UInt256.Methods.Multiply.ProductStorage
import UInt256.Safety.ArgumentValues

/-! Checked multiplication by one word: the zero and one shortcuts and the three-step carry
    ladder, composed as one path over private homes. -/

namespace UInt256Proof.Multiply.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls
open UInt256Proof.Multiply.BothTwo (run_widen_operand run_product_storage)

def scalarBody (profile : CIL.FeatureProfile) (wordIndex storageIndex : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method17 $(Lean.mkIdent `profile) $(Lean.mkIdent `wordIndex) $(Lean.mkIdent `storageIndex))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)
def scalarArgs (input : Reference) (word : BitVec 64) (output : Reference) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

theorem scalar_frame_setup (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (_found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program memory [input] [output]) :
    ∃ frame entered,
      enterFrame (scalarBody profile wordIndex storageIndex) (scalarArgs input word output) memory = .ok (frame, entered) ∧
      CompleteWritableHomes entered memory.nextIdentity (scalarBody profile wordIndex storageIndex).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords program memory entered entered [input] [output] frame (fun _ => none) := by
  have kinds : (scalarBody profile wordIndex storageIndex).localKinds = List.replicate 9 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (scalarBody profile wordIndex storageIndex)
    (by rfl) (by simp [kinds]) (by simp [kinds]) (by simp [kinds])
    (by simp [kinds]) (by simp [kinds]) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (scalarArgs input word output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

abbrev ScalarResult (original final : Memory) (input output : Reference)
    (word : BitVec 64) (returned : List Value) : Prop :=
  OutputResult original final output (inputValue original input * BitVec.ofNat 256 word.toNat) returned

theorem scalar_invoke_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[methodIndex]? = some (scalarBody profile wordIndex storageIndex)) (contract : WordContract program wordIndex) (memory : Memory) (input output : Reference)
    (word : BitVec 64) (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final,
      invoke program fuel methodIndex (scalarArgs input word output) memory = .ok (final, []) ∧
      ScalarResult memory final input output word [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := scalar_frame_setup profile program
    methodIndex wordIndex storageIndex found memory input output word call
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  let post := fun final returned => ScalarResult memory final input output word returned
  have inputFormed := state.call.input_formed (by simp : input ∈ [input])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  have started : ∃ fuel final returned,
      run program fuel methodIndex 0 (scalarArgs input word output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    cil_contract_steps 3 [scalarArgs]
    by_cases large : 1 < word.toNat
    · have greater : BitVec.ofNat 64 1 < word := large
      have flag (low incoming : BitVec 64) : BitVec.signExtend 64
          (if low + incoming < low then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) =
            sumHigh low incoming := by
        rw [← sumHigh_flag]
        split <;> rfl
      cil_contract_steps 1 [greater]
      apply run_input_to_local (argument := 0) (target := 0) state call enteredWF homes input
        (by simp) 0 (by rfl) (by rfl) found (by rfl) post
      intro _ saved0
      apply run_input_to_local (argument := 0) (target := 1) saved0 call enteredWF homes input
        (by simp) 1 (by rfl) (by rfl) found (by rfl) post
      intro _ saved1
      apply run_input_to_local (argument := 0) (target := 2) saved1 call enteredWF homes input
        (by simp) 2 (by rfl) (by rfl) found (by rfl) post
      intro _ saved2
      have reading := saved2.input_field call input (by simp) 3
      cil_contract_steps 3
        [scalarArgs, saved2.call.input_formed (by simp : input ∈ [input]), reading]
      apply WP.exists_execution
      apply run_widen_operand contract saved2 call enteredWF homes 0 4 3 _
        (by rfl) (by rfl) (by rfl) found (by rfl)
      intro _ carried0
      obtain ⟨low1, slot1, ready1, formed1⟩ := carried0.home enteredWF homes 5 (by rfl)
      cil_contract_steps (snapshots := carried0.snapshots.toLocalSnapshots)
        [scalarArgs, slot1, formed1, localAddress]
      apply WP.exists_execution
      apply run_word_call contract carried0 call homes 5 low1 word (inputLimb memory input 1)
        slot1 ready1 _ found (by rfl) (by cil_checked_step [formed1])
      intro _ product1
      have formed := product1.call.1.1
      have retained := product1.authority
      cil_contract_steps (snapshots := product1.snapshots.toLocalSnapshots) [scalarArgs]
      have carried1 := (product1.after_word_write homes (by assumption)
        localWrite).after_word_write homes (by assumption) localWrite_1
      obtain ⟨low2, slot2, ready2, formed2⟩ := carried1.home enteredWF homes 5 (by rfl)
      cil_contract_steps (snapshots := localSnapshots_1) [scalarArgs, slot2, formed2, localAddress]
      apply WP.exists_execution
      apply run_word_call contract carried1 call homes 5 low2 word (inputLimb memory input 2)
        slot2 ready2 _ found (by rfl) (by cil_checked_step [formed2])
      intro _ product2
      have formed := product2.call.1.1
      have retained := product2.authority
      cil_contract_steps (snapshots := product2.snapshots.toLocalSnapshots) [scalarArgs]
      have finished := ((product2.after_word_write homes (by assumption)
        localWrite_2).after_word_write homes (by assumption)
        localWrite_3).after_word_write homes (by assumption) localWrite_4
      cil_contract_steps (snapshots := localSnapshots_4)
        [scalarArgs, finished.call.output_formed (by simp : output ∈ [output])]
      simp only [flag, BitVec.mul_comm (inputLimb memory input 3) word]
      apply WP.exists_execution
      exact run_product_storage storage finished call owned
        (scalarLimbs (inputLimb memory input) word)
        (input_limbs_value memory input ▸ scalar_limbs_correct (inputLimb memory input) word)
        found (by rfl) (by rfl)
    · have unit : word = 0 ∨ word = 1 := by
        have cases : word.toNat = 0 ∨ word.toNat = 1 := by omega
        rcases cases with zero | one
        · left; exact BitVec.eq_of_toNat_eq zero
        · right; exact BitVec.eq_of_toNat_eq one
      rcases unit with rfl | rfl
      · cil_contract_steps 12 [scalarArgs, outputFormed]
        apply WP.exists_execution
        exact run_product_storage storage state call owned (fun _ => 0)
          (by simp [UInt256Model.value]) found (by rfl) (by rfl)
      · let bits := inputValue entered input
        have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
        obtain ⟨result, written, valid, outside, readback⟩ := state.call.write_output_slice
          (by simp : output ∈ [output]) 0 (numberBytes bits.toNat 32)
          (by rw [length]; decide) (by rw [length]; decide)
        simp only [Nat.add_zero, length] at written readback
        change write entered output (numberBytes bits.toNat 32) 1 = .ok result at written
        simp only [bits] at written length
        have loaded := input_encoded program entered [input] [output] state.call input (by simp)
        cil_contract_steps [scalarArgs, inputFormed, outputFormed]
        apply run_next_exists post found (by rfl) (by cil_checked_step [loaded])
        cil_contract_steps [written]
        refine output_result_of_storage memory entered result [input] output _ frame call valid
          owned state.caller ?_ ⟨_, readback⟩ outside
        simpa using (inputValue_of_encoded_read readback).trans
          (state.input_value call input (by simp))
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
end UInt256Proof.Multiply.ScalarSafety
