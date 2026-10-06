import UInt256.Methods.Subtract.SmallSafetySaved
import UInt256.Arithmetic.Borrow
import UInt256.Methods.Add.StorageCall
import CIL.Safety.ReturnMemory
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Subtract.Safety

open CIL.Safety

def smallStoreCall : Nat → Nat
  | 0 => Extracted.subtractScalarUInt64Body.code.findIdx fun op => match op with
      | .call callee _ => callee == Extracted.storeLimbsIndex
      | _ => false
  | n + 1 =>
      let start := smallStoreCall n + 1
      start + (Extracted.subtractScalarUInt64Body.code.drop start).findIdx fun op => match op with
        | .call callee _ => callee == Extracted.storeLimbsIndex
        | _ => false

def smallBranchFlag (branch : Fin 5) : BitVec 32 := if branch.val = 4 then 1 else 0

theorem small_return (branch : Fin 5) (args : List Value) (frame : Frame) (memory : Memory) :
    run Extracted.program (Extracted.subtractScalarUInt64Body.code.length + 1)
      Extracted.subtractScalarUInt64Index (smallStoreCall branch.val + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (smallBranchFlag branch))]) := by
  obtain ⟨branch, bound⟩ := branch
  have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals conv in (smallStoreCall _) => cbv
  all_goals
    simp only [cil_code, Nat.reduceAdd]
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, pureArity,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [run]
      simp [cil_code, step, smallBranchFlag, checkedValue, numericValue,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

def smallSelectedBranch (words : Fin 4 → BitVec 64) (word : BitVec 64) : Fin 5 :=
  if ¬ words 0 < word then 0 else if words 1 ≠ 0 then 1 else
    if words 2 ≠ 0 then 2 else if words 3 ≠ 0 then 3 else 4

/-- Follow all five actual branch endings from saved input words to the
    extracted store call with the independently specified difference limbs. -/
theorem small_branch_prefix (input output : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory) (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (formed : form memory output = .ok output)
    (slots : ∀ i : Fin 4, frame.locals[i.val]? = some (.bytes .word64 (homes i)))
    (reads : ∀ i, read memory (homes i) 8 1 = .ok (numberBytes
      (if h : i.val < 3 then words ⟨i.val + 1, by omega⟩ else words 0 - word).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.subtractScalarUInt64Index
        (smallStoreCall (smallSelectedBranch words word).val) (smallArguments input output word) frame
        [.scalar (.i64 (smallDifference words word 3)), .scalar (.i64 (smallDifference words word 2)),
         .scalar (.i64 (smallDifference words word 1)), .scalar (.i64 (smallDifference words word 0)),
         .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.subtractScalarUInt64Index smallFirstDecision
        (smallArguments input output word) frame [.scalar (.i64 word), .scalar (.i64 (words 0))]
        memory = .ok (result, returned) ∧ post result returned := by
  have s0 := slots 0
  have s1 := slots 1
  have s2 := slots 2
  have s3 := slots 3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three,
    Nat.reduceLT, ↓reduceDIte, Nat.reduceAdd] at s0 s1 s2 s3 r0 r1 r2 r3
  conv in smallFirstDecision => cbv
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : words 2 = BitVec.ofNat 64 0 <;> by_cases h3 : words 3 = BitVec.ofNat 64 0
  all_goals
    simp [BitVec.ofNat_eq_ofNat, smallSelectedBranch, smallDifference, h0, h1, h2, h3, not_true_eq_false,
      not_false_eq_true, ↓reduceIte, Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three,
      Nat.reduceEqDiff, and_true, and_false] at continuation
    conv at continuation in (smallStoreCall _) => cbv
    repeat' first
      | exact continuation
      | (solve | simpa [h0, h1, h2, h3] using continuation)
      | (simp (config := { failIfUnchanged := false }) [h0, h1, h2, h3]
         apply run_next_exists post
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [h0, h1, h2, h3, cil_code, smallArguments, step, checkedValue, numericValue, formValue, formed,
               s0, s1, s2, s3, r0, r1, r2, r3, pureArity, scalars, CIL.step, CIL.binary,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem small_selected_flag (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    smallBranchFlag (smallSelectedBranch words word) =
      (if words 0 < word ∧ words 1 = 0 ∧ words 2 = 0 ∧ words 3 = 0 then 1 else 0) := by
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : words 2 = BitVec.ofNat 64 0 <;> by_cases h3 : words 3 = BitVec.ofNat 64 0 <;>
    simp [BitVec.ofNat_eq_ofNat, smallBranchFlag, smallSelectedBranch, h0, h1, h2, h3,
      show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl]

#print axioms small_selected_flag
#print axioms small_return
#print axioms small_branch_prefix
end UInt256Proof.Subtract.Safety

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
