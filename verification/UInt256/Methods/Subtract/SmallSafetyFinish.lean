import UInt256.Methods.Subtract.SmallSafetyTail
import CIL.Safety.ReturnMemory
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

structure SmallResult (original final : Memory) (values : List Value)
    (input output : Reference) (word : BitVec 64) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = UInt256Model.value (smallDifference (inputLimb original input) word)
  flag : values = [.scalar (.i32 (smallBranchFlag (smallSelectedBranch (inputLimb original input) word)))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Finish every small-operand branch using the actual checked storage helper,
    preserving caller bytes across private-frame teardown. -/
theorem small_finish (original entered current : Memory) (frame : Frame)
    (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.subtractScalarUInt64Body (smallArguments input output word) original =
      .ok (frame, entered))
    (state : SmallSaved original entered current input output word frame.locals 4) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.subtractScalarUInt64Index smallFirstDecision
        (smallArguments input output word) frame [.scalar (.i64 word), .scalar (.i64 (inputLimb original input 0))]
        current = .ok (final, values) ∧ SmallResult original final values input output word := by
  let words := smallDifference (inputLimb original input) word
  let branch := smallSelectedBranch (inputLimb original input) word
  let post := fun final values => SmallResult original final values input output word
  have candidates := fun i : Fin 4 => state.completed i i.isLt
  let homes : Fin 4 → Reference := fun i => Classical.choose (candidates i)
  have facts := fun i => Classical.choose_spec (candidates i)
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply small_branch_prefix input output word frame current homes (inputLimb original input)
    formed (fun i => (facts i).1) (fun i => (facts i).2.2) post
  apply UInt256Proof.Safety.run_store_limbs [input] output (words 0) (words 1) (words 2) (words 3) post
    (body := Extracted.subtractScalarUInt64Body) (op := .call Extracted.storeLimbsIndex 5)
  · simp only [cil_code]
  · change Extracted.subtractScalarUInt64Body.code[smallStoreCall branch.val]? = some _
    obtain ⟨branch, bound⟩ := branch
    have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  · unfold UInt256Proof.Safety.storageArguments
    repeat' (conv in UInt256Proof.Safety.storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, words, step, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact state.call
  · intro stored valid outside authority value
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have old := (call.1.1.1 _ _ present).1
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨Extracted.subtractScalarUInt64Body.code.length + 1, leaveFrame frame stored,
      [.scalar (.i32 (smallBranchFlag branch))], small_return branch _ _ _, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation old offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, rfl, ?_, ?_⟩
    · simpa only [inputValue, bytes, UInt256Model.value] using value
    · exact (retained.access output old 32 1 true).trans (valid.1.2.2 (wordView output) (by simp))
    · intro id earlier offset untouched
      exact (retained.cells id earlier offset).trans
        ((outside id offset untouched).trans (state.preserved.cells id earlier offset))

#print axioms small_finish
theorem small_checked (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.subtractScalarUInt64Index (smallArguments input output word) memory =
        .ok (final, values) ∧ SmallResult memory final values input output word := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ := small_frame_setup memory (smallArguments input output word) call.1.1
  obtain ⟨fuel, final, values, finished, satisfied⟩ := small_input_prefix_checked memory entered input output word
    frame call setup homes (fun final values => SmallResult memory final values input output word)
    (fun current state => small_finish memory entered current frame input output word call setup state)
  have checked : (smallArguments input output word).mapM (checkedValue memory) =
      .ok (smallArguments input output word) := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [smallArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have found : Extracted.program[Extracted.subtractScalarUInt64Index]? =
      some Extracted.subtractScalarUInt64Body := by rfl
  exact ⟨fuel, final, values,
    by simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished,
    satisfied⟩

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

#print axioms SmallResult.underflow
#print axioms small_checked
#print axioms SmallResult.modular_difference
end UInt256Proof.Subtract.Safety
