import UInt256.Generated.MethodTemplates
import CIL.Safety.WordFrameSetup
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition
import CIL.Safety.CallComposition
import CIL.Safety.ReturnMemory
import CIL.Safety.Certificate
import CIL.Safety.LocalSnapshotSteps
import UInt256.Methods.Add.InputWords
import UInt256.Safety.OutputReturn
import UInt256.Arithmetic.Borrow
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Multiply.LimbStorage
import UInt256.Methods.Subtract.SafetyResult
import CIL.Safety.WeakestPrecondition

/-! Checked small-word subtraction retains saved inputs and returns the exact borrow flag. -/

namespace UInt256Proof.Subtract.Profile

-- SubtractScalarUInt64: four saved limbs, then one store and constant flag per borrow exit.
def subtractSmallBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method7 $(Lean.mkIdent `profile) $(Lean.mkIdent `storage))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety

def smallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

/-- A value whose three upper limbs or to zero is its low limb. -/
theorem input_small_value (memory : Memory) (reference : Reference)
    (small : inputLimb memory reference 1 ||| inputLimb memory reference 2 |||
      inputLimb memory reference 3 = 0) :
    inputValue memory reference = BitVec.ofNat 256 (inputLimb memory reference 0).toNat := by
  obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp small
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
  have initial : UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
    UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits)
      reference.offset
  rw [← initial, ← UInt256Proof.singleLimb_eq (inputLimb memory reference) h1 h2 h3]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- The pc of the limb-store call that ends each borrow exit. -/
def smallStoreCall : Nat → Nat
  | 0 => 22
  | 1 => 35
  | 2 => 49
  | 3 => 64
  | _ => 75

def smallBranchFlag (branch : Fin 5) : BitVec 32 := if branch.val = 4 then 1 else 0

theorem small_return (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractSmallBody profile storage))
    (branch : Fin 5) (args : List Value) (frame : Frame) (memory : Memory) :
    run program 2 method (smallStoreCall branch.val + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (smallBranchFlag branch))]) := by
  obtain ⟨branch, bound⟩ := branch
  have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals
    refine (run_next found rfl rfl).trans ?_
    exact run_return found rfl rfl rfl

def smallSelectedBranch (words : Fin 4 → BitVec 64) (word : BitVec 64) : Fin 5 :=
  if ¬ words 0 < word then 0 else if words 1 ≠ 0 then 1 else
    if words 2 ≠ 0 then 2 else if words 3 ≠ 0 then 3 else 4

/-- The comparisons that select each of the five borrow exits, in exit order. -/
theorem small_exit_cases (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    ¬ words 0 < word ∨ (words 0 < word ∧ ¬ words 1 = 0) ∨
      (words 0 < word ∧ words 1 = 0 ∧ ¬ words 2 = 0) ∨
      (words 0 < word ∧ words 1 = 0 ∧ words 2 = 0 ∧ ¬ words 3 = 0) ∨
      (words 0 < word ∧ words 1 = 0 ∧ words 2 = 0 ∧ words 3 = 0) := by
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = 0 <;>
    by_cases h2 : words 2 = 0 <;> by_cases h3 : words 3 = 0 <;> simp_all

theorem small_selected_flag (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    smallBranchFlag (smallSelectedBranch words word) =
      (if words 0 < word ∧ words 1 = 0 ∧ words 2 = 0 ∧ words 3 = 0 then 1 else 0) := by
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : words 2 = BitVec.ofNat 64 0 <;> by_cases h3 : words 3 = BitVec.ofNat 64 0 <;>
    simp [BitVec.ofNat_eq_ofNat, smallBranchFlag, smallSelectedBranch, h0, h1, h2, h3,
      show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl]

structure SmallResult (original final : Memory) (values : List Value)
    (input output : Reference) (word : BitVec 64) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = UInt256Model.value (smallDifference (inputLimb original input) word)
  flag : values = [.scalar (.i32 (smallBranchFlag (smallSelectedBranch (inputLimb original input) word)))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Save the upper limbs and the low difference, follow the selected borrow exit, and store
    through the checked limb helper; the retired frame keeps every other caller byte. -/
theorem small_checked (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final values,
      InvocationCertificate program method (smallArguments input output word) memory fuel final values ∧
      SmallResult memory final values input output word := by
  let post := fun final values => SmallResult memory final values input output word
  obtain ⟨frame, entered, setup, numeric, _, enteredFormed⟩ :=
    numeric_frame_setup (subtractSmallBody profile storage)
      (List.replicate 4 ⟨.word64, .i64 0, 0, rfl⟩) rfl rfl rfl rfl rfl memory
      (smallArguments input output word) call.1.1
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  suffices started : ∃ fuel final values,
      run program fuel method 0 (smallArguments input output word) frame [] entered =
        .ok (final, values) ∧ post final values by
    obtain ⟨fuel, final, values, finished, satisfied⟩ := started
    exact ⟨fuel, final, values, .of_run call.1.wellFormed call.2 found (checkedValues_of_valid (by
      simp [ValuesValid, smallArguments, Value.Valid, numericValue,
        call.input_formed (reference := input), call.output_formed (reference := output)]))
      setup finished, satisfied⟩
  have enteredCall := call.after_frame_setup setup
  have valid := enteredCall.1
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  cil_contract_steps (snapshots := LocalSnapshots.empty entered frame.locals) 16
    [found, smallArguments, call.input_words_kept preserved input (by simp)]
  have currentCall : CallingConditions program storedLocal_3 [input] [output] :=
    ⟨valid, write_preserves_static_world _ _ _ _ _ _ (write_preserves_static_world _ _ _ _ _ _
      (write_preserves_static_world _ _ _ _ _ _ (write_preserves_static_world _ _ _ _ _ _
        enteredCall.2 localWrite) localWrite_1) localWrite_2) localWrite_3⟩
  have formed := currentCall.output_formed (by simp : output ∈ [output])
  have exit : WP (Execution (fun fuel => run program fuel method
      (smallStoreCall (smallSelectedBranch (inputLimb memory input) word).val)
      (smallArguments input output word) frame
      [.scalar (.i64 (smallDifference (inputLimb memory input) word 3)),
        .scalar (.i64 (smallDifference (inputLimb memory input) word 2)),
        .scalar (.i64 (smallDifference (inputLimb memory input) word 1)),
        .scalar (.i64 (smallDifference (inputLimb memory input) word 0)),
        .reference (.address output)] storedLocal_3)) (Function.uncurry post) := by
    obtain ⟨childFuel, stored, invoked, valid, outside, _, value, readable⟩ :=
      UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract profile program storage
        storageFound storedLocal_3 [input] output _ _ _ _ currentCall
    have fetched : ∀ branch : Fin 5, (subtractSmallBody profile storage).code[
        smallStoreCall branch.val]? = some (.call storage 5) := by
      rintro ⟨branch, bound⟩
      have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
    have retired := output_result_of_storage memory storedLocal_3 stored [input] output _ frame
      call valid owned preserved.cells value readable outside
    exact WP.adequate.mpr (run_call_post found (fetched _)
      (by cil_checked_step [UInt256Proof.Multiply.LimbStorage.arguments, formed])
      ⟨childFuel, invoked⟩
      ⟨2, _, _, small_return program method storage profile found _ _ frame stored,
        retired.wellFormed, retired.value, rfl, retired.writable, retired.footprint⟩)
  rcases small_exit_cases (inputLimb memory input) word with taken | taken | taken | taken | taken
  all_goals
    simp only [smallSelectedBranch, smallDifference, smallStoreCall, Fin.val_zero, Fin.val_one,
      Fin.val_two, CIL.fin_val_three, Nat.reduceEqDiff, ne_eq, taken, not_true_eq_false,
      not_false_eq_true, and_true, and_false, ↓reduceIte] at exit
    cil_contract_steps (snapshots := localSnapshots_3) [smallArguments, formed, taken]
    exact WP.adequate.mp exit

/-- Arithmetic is stated over the initial input, independently of the extracted algorithm. -/
theorem SmallResult.modular_difference {original final : Memory} {values : List Value}
    {input output : Reference} {word : BitVec 64}
    (result : SmallResult original final values input output word) :
    inputValue final output = inputValue original input - BitVec.ofNat 256 word.toNat := by
  rw [result.value, small_difference_words, four_limb_difference]
  have originalValue : UInt256Model.value (inputLimb original input) = inputValue original input :=
    UInt256Proof.input_value (fun offset => (original.cells input.allocation offset).bits) input.offset
  have scalarValue : UInt256Model.value (subtractionSingleLimb word) = BitVec.ofNat 256 word.toNat := by
    simp [UInt256Model.value, subtractionSingleLimb, CIL.fin_val_three]
  rw [originalValue, scalarValue]

theorem SmallResult.underflow {original final : Memory} {values : List Value}
    {input output : Reference} {word : BitVec 64}
    (result : SmallResult original final values input output word) :
    values = [.scalar (.i32 (if (inputValue original input).toNat < word.toNat then 1 else 0))] := by
  have originalValue : UInt256Model.value (inputLimb original input) = inputValue original input :=
    UInt256Proof.input_value (fun offset => (original.cells input.allocation offset).bits) input.offset
  have scalarValue : (UInt256Model.value (singleLimb word)).toNat = word.toNat := by
    have bound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
    simp [UInt256Model.value, singleLimb, CIL.fin_val_three, Nat.mod_eq_of_lt bound]
  have flag := UInt256Proof.Reporting.small_underflow_iff (inputLimb original input) word
  rw [originalValue, scalarValue] at flag
  simpa only [small_selected_flag, flag] using result.flag

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- Subtracting a right operand of one limb through the small helper is the full subtraction. -/
theorem SmallResult.as_subtract {original current final : Memory} {values : List Value}
    {left right output : Reference}
    (result : SmallResult current final values left output (inputLimb original right 0))
    (keptRight : inputValue current right = inputValue original right)
    (small : inputLimb original right 1 ||| inputLimb original right 2 |||
      inputLimb original right 3 = 0) :
    SubtractResult current final values left right output := by
  have wide : (inputLimb original right 0).toNat < 2^256 :=
    Nat.lt_trans (inputLimb original right 0).isLt (by decide)
  refine ⟨result.wellFormed, ?_, ?_, result.writable, result.footprint⟩
  · rw [result.modular_difference, keptRight, input_small_value original right small]
  · rw [result.underflow]
    simp only [subtractUnderflow, keptRight, input_small_value original right small,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide]

/-- A child result over current caller bytes is the parent result over the original bytes. -/
theorem subtract_result_retire {program : CIL.Program} {original current final : Memory}
    {frame : Frame} {left right output : Reference} {returned : List Value}
    (call : CallingConditions program original [left, right] [output])
    (caller : ∀ id, id < original.nextIdentity → ∀ offset,
      current.cells id offset = original.cells id offset)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (result : SubtractResult current final returned left right output) :
    SubtractResult original (leaveFrame frame final) returned left right output := by
  have kept : ∀ reference ∈ [left, right],
      inputValue current reference = inputValue original reference := by
    intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    simp only [inputValue, caller reference.allocation (call.1.1.1 _ _ present).1]
  have retained := leaveFrame_preserves_memory_below frame final original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ :=
    formed_reference_live _ _ _ (call.output_formed (by simp : output ∈ [output]))
  have old := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame final).cells output.allocation offset).bits) =
      (fun offset => (final.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation old offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ result.wellFormed, ?_, ?_,
    (retained.access output old 32 1 true).trans result.writable, ?_⟩
  · have math := result.value
    rw [kept left (by simp), kept right (by simp)] at math
    simpa only [inputValue, bytes] using math
  · rw [result.flag]
    simp only [subtractUnderflow, kept left (by simp), kept right (by simp)]
  · intro id bound offset outside
    exact (retained.cells id bound offset).trans ((result.footprint id
      (Nat.lt_of_lt_of_le bound next) offset outside).trans (caller id bound offset))

end UInt256Proof.Subtract.Profile
