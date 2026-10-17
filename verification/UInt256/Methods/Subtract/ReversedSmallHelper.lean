import UInt256.Methods.Subtract.ReversedStorage

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety

/-- SubtractScalarUInt64 pushing its words high first for the reversed StoreLimbs. -/
def subtractReversedSmallBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method :=
  { subtractSmallBody profile storage with code := [
  .arg 0, .fieldAt 0 8, .arg 0, .fieldAt 8 8, .setLocal 0, .arg 0, .fieldAt 16 8, .setLocal 1,
  .arg 0, .fieldAt 24 8, .setLocal 2, .dup, .arg 1, .sub, .setLocal 3, .arg 1, .bltu 25,
  .arg 2, .local 2, .local 1, .local 0, .local 3, .call storage 5, .const32 0, .ret (some .unsigned8),
  .local 0, .brzero 38,
  .arg 2, .local 2, .local 1, .local 0, .const32 1, .convI8, .sub, .local 3,
  .call storage 5, .const32 0, .ret (some .unsigned8),
  .local 1, .brzero 52,
  .arg 2, .local 2, .local 1, .const32 1, .convI8, .sub, .const32 (BitVec.ofInt 32 (-1)), .convI8, .local 3,
  .call storage 5, .const32 0, .ret (some .unsigned8),
  .local 2, .brzero 67,
  .arg 2, .local 2, .const32 1, .convI8, .sub, .const32 (BitVec.ofInt 32 (-1)), .convI8,
  .const32 (BitVec.ofInt 32 (-1)), .convI8, .local 3,
  .call storage 5, .const32 0, .ret (some .unsigned8),
  .arg 2, .const32 (BitVec.ofInt 32 (-1)), .convI8, .const32 (BitVec.ofInt 32 (-1)), .convI8,
  .const32 (BitVec.ofInt 32 (-1)), .convI8, .local 3,
  .call storage 5, .const32 1, .ret (some .unsigned8)] }

/-- Steps only read the profile and return kind, which the reversed body shares. -/
theorem reversed_small_step (profile : CIL.FeatureProfile) (storage : Nat) (op : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) :
    step (subtractReversedSmallBody profile storage) op pc args frame stack memory =
      step (subtractSmallBody profile storage) op pc args frame stack memory := rfl

theorem reversed_small_enter (profile : CIL.FeatureProfile) (storage : Nat) (args : List Value) (memory : Memory) :
    enterFrame (subtractReversedSmallBody profile storage) args memory =
      enterFrame (subtractSmallBody profile storage) args memory := rfl

/-- Save the upper limbs and the low difference, keeping the low limb for the first borrow test. -/
theorem reversed_small_input_prefix_checked (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractReversedSmallBody profile storage)) (original entered : Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (subtractSmallBody profile storage) (smallArguments input output word) original =
      .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity smallWordSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, SmallSaved program original entered after input output word frame.locals 4 →
      ∃ fuel result returned,
        run program fuel method 16 (smallArguments input output word) frame
          [.scalar (.i64 word), .scalar (.i64 (inputLimb original input 0))] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 (smallArguments input output word) frame [] entered = .ok (result, returned) ∧
        post result returned := by
  have enteredCall := call.after_frame_setup setup
  have initial : SmallSaved program original entered entered input output word frame.locals 0 :=
    ⟨enteredCall, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow, by intro i impossible; omega⟩
  obtain ⟨first, saved1, step0⟩ := initial.save (profile := profile) (storage := storage) 0 call enteredCall.1.1 homes
  obtain ⟨second, saved2, step1⟩ := saved1.save (profile := profile) (storage := storage) 1 call enteredCall.1.1 homes
  obtain ⟨third, saved3, step2⟩ := saved2.save (profile := profile) (storage := storage) 2 call enteredCall.1.1 homes
  obtain ⟨fourth, saved4, step3⟩ := saved3.save (profile := profile) (storage := storage) 3 call enteredCall.1.1 homes
  have done := continuation fourth saved4
  have f0 := enteredCall.input_formed (reference := input) (by simp)
  have f1 := saved1.call.input_formed (reference := input) (by simp)
  have f2 := saved2.call.input_formed (reference := input) (by simp)
  have r0 := call.input_field_after_setup setup (by simp : input ∈ [input]) 0
  have r1 := call.input_field_after_setup setup (by simp : input ∈ [input]) 1
  simp only [Fin.val_zero, Fin.val_one, Nat.reduceMul] at r0 r1
  have r2 (rest : List Value) : instruction (.fieldAt 16 8) (.reference (.address input) :: rest) first =
      .ok (first, .scalar (.i64 (inputLimb original input 2)) :: rest) := by
    have field := saved1.call.input_field_instruction (reference := input) (by simp) 2 rest
    simp only [Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at field
    rw [field]
    simp only [inputLimb, call.input_bytes_of_memory_below saved1.preserved (reference := input) (by simp)]
  have r3 (rest : List Value) : instruction (.fieldAt 24 8) (.reference (.address input) :: rest) second =
      .ok (second, .scalar (.i64 (inputLimb original input 3)) :: rest) := by
    have field := saved2.call.input_field_instruction (reference := input) (by simp) 3 rest
    simp only [Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at field
    rw [field]
    simp only [inputLimb, call.input_bytes_of_memory_below saved2.preserved (reference := input) (by simp)]
  simp only [smallSavedWord, Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three,
    Nat.reduceLT, ↓reduceDIte, Nat.reduceAdd] at step0 step1 step2 step3
  repeat' first
    | exact done
    | (simp (config := { failIfUnchanged := false })
       apply run_next_exists post found (by rfl)
       rw [reversed_small_step]
       first
       | exact step0 _ _
       | exact step1 _ _
       | exact step2 _ _
       | exact step3 _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, smallArguments, checkedValue, numericValue, formValue, f0, f1, f2,
             r0, r1, r2, r3, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedAt,
             Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

theorem reversed_small_return (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractReversedSmallBody profile storage))
    (branch : Fin 5) (args : List Value) (frame : Frame) (memory : Memory) :
    run program 2 method (smallStoreCall branch.val + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (smallBranchFlag branch))]) := by
  obtain ⟨branch, bound⟩ := branch
  have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [smallStoreCall, Nat.reduceAdd]
    apply Eq.trans
    · apply run_next found (by rfl)
      rw [reversed_small_step]
      simp (config := { implicitDefEqProofs := false })
        [step, pureArity, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · simp [run, found, subtractReversedSmallBody, subtractSmallBody, step, CIL.NarrowKind.extend, smallBranchFlag,
        checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Follow all five branch endings from the saved words to the store call with the words high first. -/
theorem reversed_small_branch_prefix (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractReversedSmallBody profile storage))
    (input output : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory) (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (formed : form memory output = .ok output)
    (slots : ∀ i : Fin 4, frame.locals[i.val]? = some (.bytes .word64 (homes i)))
    (reads : ∀ i, read memory (homes i) 8 1 = .ok (numberBytes
      (if h : i.val < 3 then words ⟨i.val + 1, by omega⟩ else words 0 - word).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method
        (smallStoreCall (smallSelectedBranch words word).val) (smallArguments input output word) frame
        [.scalar (.i64 (smallDifference words word 0)), .scalar (.i64 (smallDifference words word 1)),
         .scalar (.i64 (smallDifference words word 2)), .scalar (.i64 (smallDifference words word 3)),
         .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 16
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
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : words 2 = BitVec.ofNat 64 0 <;> by_cases h3 : words 3 = BitVec.ofNat 64 0
  all_goals
    simp [BitVec.ofNat_eq_ofNat, smallSelectedBranch, smallDifference, h0, h1, h2, h3, not_true_eq_false,
      not_false_eq_true, ↓reduceIte, Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three,
      Nat.reduceEqDiff, and_true, and_false, smallStoreCall] at continuation
    repeat' first
      | exact continuation
      | (solve | simpa [h0, h1, h2, h3] using continuation)
      | (simp (config := { failIfUnchanged := false }) [h0, h1, h2, h3]
         apply run_next_exists post found (by rfl)
         rw [reversed_small_step]
         simp (config := { implicitDefEqProofs := false })
           [h0, h1, h2, h3, smallArguments, step, checkedValue, numericValue, formValue, formed,
             s0, s1, s2, s3, r0, r1, r2, r3, pureArity, scalars, CIL.step, CIL.binary, CIL.unary,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms reversed_small_input_prefix_checked
#print axioms reversed_small_return
#print axioms reversed_small_branch_prefix
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety

/-- Every small-operand branch stores through the reversed limb helper and keeps caller bytes. -/
theorem reversed_small_finish (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractReversedSmallBody profile storage))
    (storageFound : program[storage]? = some (reversedStorageBody profile))
    (original entered current : Memory) (frame : Frame)
    (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (subtractSmallBody profile storage) (smallArguments input output word) original =
      .ok (frame, entered))
    (state : SmallSaved program original entered current input output word frame.locals 4) :
    ∃ fuel final values,
      run program fuel method 16
        (smallArguments input output word) frame [.scalar (.i64 word), .scalar (.i64 (inputLimb original input 0))]
        current = .ok (final, values) ∧ SmallResult original final values input output word := by
  let words := smallDifference (inputLimb original input) word
  let branch := smallSelectedBranch (inputLimb original input) word
  let post := fun final values => SmallResult original final values input output word
  have candidates := fun i : Fin 4 => state.completed i i.isLt
  let homes : Fin 4 → Reference := fun i => Classical.choose (candidates i)
  have facts := fun i => Classical.choose_spec (candidates i)
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply reversed_small_branch_prefix program method storage profile found input output word frame current homes
    (inputLimb original input) formed (fun i => (facts i).1) (fun i => (facts i).2.2) post
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    reversed_store_limbs_readable_contract profile program storage storageFound
      current [input] output (words 0) (words 1) (words 2) (words 3) state.call
  have fetched : (subtractReversedSmallBody profile storage).code[smallStoreCall branch.val]? =
      some (.call storage 5) := by
    obtain ⟨branch, bound⟩ := branch
    have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  have stepped : step (subtractReversedSmallBody profile storage) (.call storage 5) (smallStoreCall branch.val)
      (smallArguments input output word) frame
      [.scalar (.i64 (words 0)), .scalar (.i64 (words 1)), .scalar (.i64 (words 2)),
        .scalar (.i64 (words 3)), .reference (.address output)] current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 3) (words 2) (words 1) (words 0))
        [] current) := by
    rw [reversed_small_step]
    simp [step, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  have returned := reversed_small_return program method storage profile found branch (smallArguments input output word)
    frame stored
  obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨childFuel, invoked⟩ ⟨2, returned⟩
  refine ⟨fuel, leaveFrame frame stored, _, executed, ?_⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have old := (call.1.1.1 _ _ present).1
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
    (fun id member => (fresh.2 id member).1)
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

/-- Checked invocation of the reversed small helper with the shared small-result guarantees. -/
theorem reversed_small_checked (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractReversedSmallBody profile storage))
    (storageFound : program[storage]? = some (reversedStorageBody profile)) :
    SmallChecked program method := by
  intro memory input output word call
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    small_frame_setup profile storage memory (smallArguments input output word) call.1.1
  obtain ⟨fuel, final, values, finished, satisfied⟩ := reversed_small_input_prefix_checked program method storage
    profile found memory entered input output word frame call setup homes
    (fun final values => SmallResult memory final values input output word)
    (fun current state => reversed_small_finish program method storage profile found storageFound memory entered
      current frame input output word call setup state)
  have checked : (smallArguments input output word).mapM (checkedValue memory) =
      .ok (smallArguments input output word) := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [smallArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have reversedSetup : enterFrame (subtractReversedSmallBody profile storage) (smallArguments input output word)
      memory = .ok (frame, entered) := setup
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked reversedSetup
  exact ⟨fuel, final, values,
    certify_invocation program method _ _ memory frame entered fuel final values found checked reversedSetup live
      finished,
    satisfied⟩

#print axioms reversed_small_finish
#print axioms reversed_small_checked
end UInt256Proof.Subtract.Profile
