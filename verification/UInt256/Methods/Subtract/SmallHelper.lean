import CIL.Safety.WordFrameSetup
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition
import CIL.Safety.CallComposition
import CIL.Safety.ReturnMemory
import CIL.Safety.Certificate
import UInt256.Safety.CallerSetup
import UInt256.Arithmetic.Borrow
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Multiply.LimbStorage
import CIL.Safety.MethodContract

namespace UInt256Proof.Subtract.Profile

-- SubtractScalarUInt64: four saved limbs, then one store and constant flag per borrow exit.
def subtractSmallBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.i64 0, .i64 0, .i64 0, .i64 0], localKinds := [.word64, .word64, .word64, .word64], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .arg 0,
  .fieldAt 8 8,
  .setLocal 0,
  .arg 0,
  .fieldAt 16 8,
  .setLocal 1,
  .arg 0,
  .fieldAt 24 8,
  .setLocal 2,
  .dup,
  .arg 1,
  .sub,
  .setLocal 3,
  .arg 1,
  .bltu 25,
  .arg 2,
  .local 3,
  .local 0,
  .local 1,
  .local 2,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .local 0,
  .brzero 38,
  .arg 2,
  .local 3,
  .local 0,
  .const32 1,
  .convI8,
  .sub,
  .local 1,
  .local 2,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .local 1,
  .brzero 52,
  .arg 2,
  .local 3,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .local 1,
  .const32 1,
  .convI8,
  .sub,
  .local 2,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .local 2,
  .brzero 67,
  .arg 2,
  .local 3,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .local 2,
  .const32 1,
  .convI8,
  .sub,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .arg 2,
  .local 3,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .call storage 5,
  .const32 1,
  .ret (some .unsigned8)] }
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety

def smallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

def smallWordSpecs : List (Option (BitVec 64)) := [some 0, some 0, some 0, some 0]

theorem small_frame_setup (profile : CIL.FeatureProfile) (storage : Nat) (memory : Memory) (args : List Value)
    (wf : memory.WellFormed) :
    ∃ frame result,
      enterFrame (subtractSmallBody profile storage) args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity smallWordSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  word_frame_setup (subtractSmallBody profile storage) smallWordSpecs (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) memory args wf

/-- A private word store retains the caller snapshot and all frame access authority. -/
theorem small_private_store (program : CIL.Program) (profile : CIL.FeatureProfile) (storage : Nat)
    (original entered current : CIL.Safety.Memory)
    (input output : Reference) (word value : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (currentCall : CallingConditions program current [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (initial : BitVec 64)
    (specified : smallWordSpecs[index]? = some (some initial)) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes .word64 reference) ∧
      read after reference 8 1 = .ok (numberBytes value.toNat 8) ∧
      MemoryBelow original.nextIdentity original after ∧
      CallingConditions program after [input] [output] ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes value.toNat 8) 1 = .ok after ∧
      ∀ pc rest, step (subtractSmallBody profile storage) (.setLocal index) pc
        (smallArguments input output word) frame (.scalar (.i64 value) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.word_at index initial specified
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have old := (enteredWF.1 reference.allocation allocation ready.present).1
  have permitted := authority.access writable old
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 value permitted
  have caller := preserved.trans (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have afterWF := write_preserves_wellFormed _ _ _ _ _ currentCall.1.1 written
  have afterWorld := write_preserves_static_world _ _ _ _ _ _ currentCall.2 written
  refine ⟨reference, after, slot, loaded, caller,
    call.after_memory_below caller afterWF afterWorld,
    authority.trans (write_preserves_access_below written _), written, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := subtractSmallBody profile storage) (pc := pc)
    (args := smallArguments input output word) (rest := rest) value slot permitted
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

theorem small_input_spec (i : Fin 4) : smallWordSpecs[i.val]? = some (some 0) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

def smallSavedWord (original : Memory) (input : Reference) (word : BitVec 64) (i : Fin 4) : BitVec 64 :=
  if h : i.val < 3 then inputLimb original input ⟨i.val + 1, by omega⟩ else inputLimb original input 0 - word

structure SmallSaved (program : CIL.Program) (original entered current : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64) (slots : List LocalSlot) (done : Nat) : Prop where
  call : CallingConditions program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  completed : ∀ i : Fin 4, i.val < done → ∃ reference,
    slots[i.val]? = some (.bytes .word64 reference) ∧ reference.allocation < entered.nextIdentity ∧
      read current reference 8 1 = .ok (numberBytes (smallSavedWord original input word i).toNat 8)

theorem SmallSaved.save {program : CIL.Program} {profile : CIL.FeatureProfile} {storage : Nat}
    {original entered current : CIL.Safety.Memory}
    {input output : Reference} {word : BitVec 64} {frame : Frame}
    (index : Fin 4)
    (state : SmallSaved program original entered current input output word frame.locals index.val)
    (call : CallingConditions program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs frame.locals) :
    ∃ after, SmallSaved program original entered after input output word frame.locals (index.val + 1) ∧
      ∀ pc rest, step (subtractSmallBody profile storage) (.setLocal index.val) pc
        (smallArguments input output word) frame
        (.scalar (.i64 (smallSavedWord original input word index)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, fullSlot, loaded, preserved, afterCall, authority, written, stepped⟩ :=
    small_private_store program profile storage original entered current input output word
      (smallSavedWord original input word index)
      frame call state.call enteredWF homes state.preserved state.authority
      index.val 0 (small_input_spec index)
  have slot := fullSlot
  obtain ⟨home, homeSlot, _, _, writable⟩ := homes.word_at index.val 0 (small_input_spec index)
  have same : home = reference := by rw [slot] at homeSlot; simpa using homeSlot.symm
  subst home
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have old := (enteredWF.1 _ _ ready.present).1
  refine ⟨after, ⟨afterCall, preserved, authority, ?_⟩, stepped⟩
  intro i saved
  by_cases equal : i = index
  · subst i
    exact ⟨reference, slot, old, loaded⟩
  · have earlier : i.val < index.val := by
      have different : i.val ≠ index.val := fun h => equal (Fin.ext h)
      omega
    obtain ⟨previous, previousSlot, previousOld, previousRead⟩ := state.completed i earlier
    have different := Nat.ne_of_lt (homes.ordered i.val index.val previous reference earlier previousSlot slot)
    refine ⟨previous, previousSlot, previousOld,
      (write_preserves_access_below written entered.nextIdentity).read_eq previousRead previousOld ?_⟩
    intro offset _
    exact write_word_outside written _ _ (Or.inl different)

/-- Save the upper limbs and the low difference, keeping the low limb for the first borrow test. -/
theorem small_input_prefix_checked (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractSmallBody profile storage)) (original entered : Memory)
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
  have r2 (rest : List Value) : instruction (.fieldAt 16 8) (.reference (.address input) :: rest) first =
      .ok (first, .scalar (.i64 (inputLimb original input 2)) :: rest) := by
    have field := saved1.call.input_field_instruction (reference := input) (by simp) 2 rest
    simp only [Fin.val_two, Nat.reduceMul] at field
    rw [field]
    simp only [inputLimb, call.input_bytes_of_memory_below saved1.preserved (reference := input) (by simp)]
  have r3 (rest : List Value) : instruction (.fieldAt 24 8) (.reference (.address input) :: rest) second =
      .ok (second, .scalar (.i64 (inputLimb original input 3)) :: rest) := by
    have field := saved2.call.input_field_instruction (reference := input) (by simp) 3 rest
    simp only [CIL.fin_val_three, Nat.reduceMul] at field
    rw [field]
    simp only [inputLimb, call.input_bytes_of_memory_below saved2.preserved (reference := input) (by simp)]
  cil_contract_steps 4 [smallArguments, f0, r0, r1]
  refine run_next_exists post found rfl (step0 _ _) ?_
  cil_contract_steps 2 [smallArguments, f1, r2]
  refine run_next_exists post found rfl (step1 _ _) ?_
  cil_contract_steps 2 [smallArguments, f2, r3]
  refine run_next_exists post found rfl (step2 _ _) ?_
  cil_contract_steps 3 []
  refine run_next_exists post found rfl (step3 _ _) ?_
  cil_contract_steps [] until done

#print axioms small_frame_setup
#print axioms small_private_store
#print axioms SmallSaved.save
#print axioms small_input_prefix_checked
end UInt256Proof.Subtract.Profile


namespace UInt256Proof.Subtract.Profile
open CIL.Safety

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

set_option hygiene false in
/-- Step one branch ending to its store call and match the selected continuation. -/
macro "small_branch_leaf" " [" cases:term,* "]" : tactic => `(tactic| (
  cil_contract_steps [smallArguments, formed, slots, loads, bne_iff_ne, ne_eq, eq_self_iff_true,
    not_true_eq_false, not_false_eq_true, ite_true, ite_false, $[$cases:term],*]
  simp only [smallSelectedBranch, smallDifference, smallStoreCall, Fin.val_zero, Fin.val_one, Fin.val_two,
    CIL.fin_val_three, Nat.reduceEqDiff, ne_eq, not_false_eq_true, not_true_eq_false, and_true, and_false,
    ↓reduceIte, $[$cases:term],*] at continuation
  exact continuation))

/-- Follow all five branch endings from the saved words to the store call with the specified limbs. -/
theorem small_branch_prefix (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractSmallBody profile storage))
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
        [.scalar (.i64 (smallDifference words word 3)), .scalar (.i64 (smallDifference words word 2)),
         .scalar (.i64 (smallDifference words word 1)), .scalar (.i64 (smallDifference words word 0)),
         .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 16
        (smallArguments input output word) frame [.scalar (.i64 word), .scalar (.i64 (words 0))]
        memory = .ok (result, returned) ∧ post result returned := by
  have loads := fun i => load_local_word64_of_read (reads i)
  by_cases h0 : words 0 < word
  · by_cases h1 : words 1 = 0
    · by_cases h2 : words 2 = 0
      · by_cases h3 : words 3 = 0 <;> small_branch_leaf [h0, h1, h2, h3]
      · small_branch_leaf [h0, h1, h2]
    · small_branch_leaf [h0, h1]
  · small_branch_leaf [h0]

theorem small_selected_flag (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    smallBranchFlag (smallSelectedBranch words word) =
      (if words 0 < word ∧ words 1 = 0 ∧ words 2 = 0 ∧ words 3 = 0 then 1 else 0) := by
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : words 2 = BitVec.ofNat 64 0 <;> by_cases h3 : words 3 = BitVec.ofNat 64 0 <;>
    simp [BitVec.ofNat_eq_ofNat, smallBranchFlag, smallSelectedBranch, h0, h1, h2, h3,
      show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl]

#print axioms small_return
#print axioms small_branch_prefix
#print axioms small_selected_flag
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety

structure SmallResult (original final : Memory) (values : List Value)
    (input output : Reference) (word : BitVec 64) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = UInt256Model.value (smallDifference (inputLimb original input) word)
  flag : values = [.scalar (.i32 (smallBranchFlag (smallSelectedBranch (inputLimb original input) word)))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Every small-operand branch stores through the checked limb helper and keeps caller bytes. -/
theorem small_finish (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
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
  apply small_branch_prefix program method storage profile found input output word frame current homes
    (inputLimb original input) formed (fun i => (facts i).1) (fun i => (facts i).2.2) post
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract profile program storage storageFound
      current [input] output (words 0) (words 1) (words 2) (words 3) state.call
  have fetched : (subtractSmallBody profile storage).code[smallStoreCall branch.val]? = some (.call storage 5) := by
    obtain ⟨branch, bound⟩ := branch
    have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  have stepped : step (subtractSmallBody profile storage) (.call storage 5) (smallStoreCall branch.val)
      (smallArguments input output word) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3)) [] current) := by
    simp [step, cil_guard, observerCount, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  have returned := small_return program method storage profile found branch (smallArguments input output word) frame stored
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

theorem small_checked (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final values,
      InvocationCertificate program method (smallArguments input output word) memory fuel final values ∧
      SmallResult memory final values input output word := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    small_frame_setup profile storage memory (smallArguments input output word) call.1.1
  obtain ⟨fuel, final, values, finished, satisfied⟩ := small_input_prefix_checked program method storage profile found
    memory entered input output word frame call setup homes (fun final values => SmallResult memory final values input output word)
    (fun current state => small_finish program method storage profile found storageFound memory entered current frame
      input output word call setup state)
  have checked : (smallArguments input output word).mapM (checkedValue memory) =
      .ok (smallArguments input output word) := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [smallArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, values,
    certify_invocation program method _ _ memory frame entered fuel final values found checked setup live finished,
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

#print axioms small_finish
#print axioms small_checked
#print axioms SmallResult.modular_difference
#print axioms SmallResult.underflow
end UInt256Proof.Subtract.Profile
