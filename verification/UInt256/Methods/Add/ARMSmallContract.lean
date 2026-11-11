import UInt256.Methods.Add.ARMSmallState
import CIL.Safety.LocalSnapshotSteps

/-! Checked small-add execution, arithmetic, overflow and caller-memory contracts. -/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Increment one saved limb during carry propagation. -/
def armIncrementWord (words : Fin 4 → BitVec 64) (index : Fin 4) : Fin 4 → BitVec 64 :=
  fun i => if i.val = index.val then words index + 1 else words i

/-- Propagate a low-limb carry and report overflow past the highest limb. -/
def armCarryResult (words : Fin 4 → BitVec 64) : (Fin 4 → BitVec 64) × BitVec 32 :=
  let first := armIncrementWord words 1
  if first 1 = BitVec.ofNat 64 0 then
    let second := armIncrementWord first 2
    if second 2 = BitVec.ofNat 64 0 then
      let third := armIncrementWord second 3
      (third, if third 3 = BitVec.ofNat 64 0 then 1 else 0)
    else (second, 0)
  else (first, 0)

/-- The saved limbs and overflow bit after adding the low word. -/
def armSmallResult (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    (Fin 4 → BitVec 64) × BitVec 32 :=
  if words 0 + word < words 0 then armCarryResult words else (words, 0)

/-- Execution's explicit limb updates equal the independently proved small sum. -/
theorem arm_small_result_words (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    armSmallOutputWords (armSmallResult words word).1 (words 0 + word) =
      UInt256Proof.smallResult words word := by
  by_cases carry : words 0 + word < words 0 <;>
    by_cases first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
  all_goals
    funext ⟨i, bound⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [armSmallOutputWords, armSmallResult, armCarryResult, armIncrementWord,
        UInt256Proof.smallResult, carry, first, second,
        show (3 : Fin 4).val = 3 from rfl]

theorem arm_small_result_value (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference)
    (word : BitVec 64) :
    UInt256Model.value (armSmallOutputWords (armSmallResult (inputLimb memory input) word).1
      (inputLimb memory input 0 + word)) = inputValue memory input + BitVec.ofNat 256 word.toNat := by
  rw [arm_small_result_words, UInt256Proof.small_result_sum]
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [initial]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- The returned byte bit is exactly overflow of the mathematical 256-bit sum. -/
theorem arm_small_result_flag (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    (armSmallResult words word).2 =
      if 2^256 ≤ (UInt256Model.value words).toNat + word.toNat then 1 else 0 := by
  have overflow := UInt256Proof.Reporting.small_overflow_iff words word
  have wideBound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
  have single : (UInt256Model.value (UInt256Proof.singleLimb word)).toNat = word.toNat := by
    simp [UInt256Model.value, UInt256Proof.singleLimb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound]
  rw [single] at overflow
  simp only [← overflow]
  by_cases carry : words 0 + word < words 0 <;>
    by_cases first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases third : words 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
  all_goals
    simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second, third,
      show (3 : Fin 4).val = 3 from rfl]

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Exact sum and overflow, writable output and preservation of all other caller bytes. -/
structure ARMSmallPost (original final : Memory) (returned : List Value)
    (input output : Reference) (word : BitVec 64) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original input + BitVec.ofNat 256 word.toNat
  flag : returned = [.scalar (.i32 (if 2^256 ≤ (inputValue original input).toNat + word.toNat then 1 else 0))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Full extracted ARM helper execution satisfies independent addition and exact overflow,
    retiring private storage while preserving every other caller byte. -/
theorem arm_small_entry (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage))
    (enabled : profile.advSimd = true)
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (armSmallBody profile storage) (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    WP (Execution (fun fuel => run program fuel method 0
      (armSmallArguments input output word) frame [] entered))
      (fun result => ARMSmallPost original result.1 result.2 input output word) := by
  let post := fun final returned => ARMSmallPost original final returned input output word
  let args := armSmallArguments input output word
  let words := inputLimb original input
  let sum := words 0 + word
  let result := armSmallResult words word
  let execute := fun pc stack memory => WP
    (Execution (fun fuel => run program fuel method pc args frame stack memory))
    (Function.uncurry post)
  have enteredCall := call.after_frame_setup setup
  have initial : ARMSmallSaved program original entered entered input output frame 0 :=
    ⟨enteredCall, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow, by
        intro index value impossible
        simp [smallSaved] at impossible⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have finish (current : Memory)
      (state : SmallState program original entered current input output frame
        (armSmallKnown result.1 sum result.2)) : execute 47 [] current := by
    generalize computed : result = calculated at state
    have flagFit : CIL.NarrowKind.unsigned8.extend calculated.2 = calculated.2 := by
      rw [← computed]
      change CIL.NarrowKind.unsigned8.extend (armSmallResult words word).2 = _
      rw [arm_small_result_flag]
      split <;> rfl
    have suffix : execute 52
        [.scalar (.i64 (calculated.1 3)), .scalar (.i64 (calculated.1 2)),
          .scalar (.i64 (calculated.1 1)), .scalar (.i64 sum), .reference (.address output)]
        current := by
      apply arm_small_store_return program method storage profile found storageFound current entered
        original.nextIdentity frame args [input] output
        (armSmallOutputWords calculated.1 sum) calculated.2
        _ state.call homes state.snapshots (by rfl) flagFit outputOld post
      intro stored valid outside _ value
      have fresh := enterFrame_fresh _ _ _ _ _ setup
      have retired := leaveFrame_preserves_memory_below frame stored original.nextIdentity
        (fun id member => (fresh.2 id member).1)
      have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
          (fun offset => (stored.cells output.allocation offset).bits) := by
        funext offset
        rw [retired.cells output.allocation outputOld offset]
      refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
      · have mathematical := value.trans (by
          simpa only [← computed] using arm_small_result_value original input word)
        simpa only [inputValue, bytes] using mathematical
      · have initialValue : UInt256Model.value words = inputValue original input :=
          UInt256Proof.input_value (fun offset => (original.cells input.allocation offset).bits)
            input.offset
        have exactFlag := arm_small_result_flag words word
        rw [initialValue] at exactFlag
        simp only [← computed, result, exactFlag]
      · exact (retired.access output outputOld 32 1 true).trans
          (valid.1.writable (wordView output) (by simp))
      · intro id old offset untouched
        exact (retired.cells id old offset).trans
          ((outside id offset untouched).trans (state.preserved.cells id old offset))
    cil_contract_steps (snapshots := state.snapshots)
      [args, armSmallArguments, armSmallKnown, smallSaved,
        state.call.output_formed (reference := output) (by simp)] until suffix
  obtain ⟨first, saved1, store0⟩ := initial.save 0 (armSmallBody profile storage) enteredCall.1.1 homes
  obtain ⟨second, saved2, store1⟩ := saved1.save 1 (armSmallBody profile storage) enteredCall.1.1 homes
  obtain ⟨third, saved3, store2⟩ := saved2.save 2 (armSmallBody profile storage) enteredCall.1.1 homes
  obtain ⟨fourth, saved4, store3⟩ := saved3.save 3 (armSmallBody profile storage) enteredCall.1.1 homes
  obtain ⟨summed, sumState, storeSum⟩ := saved4.store (armSmallBody profile storage)
    enteredCall.1.1 homes 5 armWordSpec (by rfl) (.i64 sum) sum.toNat rfl
  obtain ⟨ready, state, storeFlag⟩ := sumState.store (armSmallBody profile storage)
    enteredCall.1.1 homes 6 ⟨.narrow .unsigned8, .i32 0, 0, rfl⟩ (by rfl) (.i32 0) 0 rfl
  change SmallState program original entered ready input output frame
    (armSmallKnown words sum 0) at state
  have arithmetic : execute 20 [] ready := by
    have complementary : (words 0 ≤ sum) = (¬ sum < words 0) := by
      apply propext
      simp only [BitVec.le_def, BitVec.lt_def, Nat.not_lt]
    by_cases carry : sum < words 0
    · have carryPath : execute 23 [] ready := by
        obtain ⟨after1, state1, increment1⟩ := state.store (armSmallBody profile storage)
          enteredCall.1.1 homes 1 armWordSpec (by rfl) (.i64 (words 1 + 1)) _ rfl
        simp only [armWordSpec, localResult] at state1
        rw [armSmallKnown_store_word _ _ _ 1 (by decide)] at state1
        have branch1 : execute 29 [.scalar (.i64 (words 1 + 1))] after1 := by
          by_cases zero1 : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
          · obtain ⟨after2, state2, increment2⟩ := state1.store (armSmallBody profile storage)
              enteredCall.1.1 homes 2 armWordSpec (by rfl) (.i64 (words 2 + 1)) _ rfl
            simp only [armWordSpec, localResult] at state2
            rw [armSmallKnown_store_word _ _ _ 2 (by decide)] at state2
            have branch2 : execute 36 [.scalar (.i64 (words 2 + 1))] after2 := by
              by_cases zero2 : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
              · obtain ⟨after3, state3, increment3⟩ := state2.store (armSmallBody profile storage)
                  enteredCall.1.1 homes 3 armWordSpec (by rfl) (.i64 (words 3 + 1)) _ rfl
                simp only [armWordSpec, localResult] at state3
                rw [armSmallKnown_store_word _ _ _ 3 (by decide)] at state3
                let flag : BitVec 32 := if words 3 + 1 = BitVec.ofNat 64 0 then 1 else 0
                obtain ⟨afterFlag, finalState, flagStore⟩ := state3.store (armSmallBody profile storage)
                  enteredCall.1.1 homes 6 ⟨.narrow .unsigned8, .i32 0, 0, rfl⟩ (by rfl)
                  (.i32 flag) flag.toNat (by dsimp [flag]; split <;> rfl)
                have flagFit : CIL.NarrowKind.unsigned8.extend flag = flag := by
                  dsimp only [flag]; split <;> rfl
                simp only [localResult, flagFit, armSmallKnown_store_flag] at finalState
                have final : execute 47 [] afterFlag := by
                  apply finish afterFlag
                  dsimp only [result, armSmallResult, armCarryResult]
                  unfold armIncrementWord
                  simpa [show words 0 + word = sum from rfl, carry, zero1, zero2, flag,
                    Fin.ext_iff, show (1 : Fin 4).val = 1 from rfl,
                    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl] using finalState
                cil_contract_steps (snapshots := state2.snapshots)
                  [zero2, increment3, flagStore, flag, armSmallKnown, smallSaved] until final
              · have final : execute 47 [] after2 := by
                  apply finish after2
                  dsimp only [result, armSmallResult, armCarryResult]
                  unfold armIncrementWord
                  simpa [show words 0 + word = sum from rfl, carry, zero1, zero2,
                    Fin.ext_iff, show (1 : Fin 4).val = 1 from rfl,
                    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl] using state2
                cil_contract_steps [zero2] until final
            cil_contract_steps (snapshots := state1.snapshots)
              [zero1, increment2, armSmallKnown, smallSaved] until branch2
          · have final : execute 47 [] after1 := by
              apply finish after1
              dsimp only [result, armSmallResult, armCarryResult]
              unfold armIncrementWord
              simpa [show words 0 + word = sum from rfl, carry, zero1,
                Fin.ext_iff, show (1 : Fin 4).val = 1 from rfl,
                show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl] using state1
            cil_contract_steps [zero1] until final
        cil_contract_steps (snapshots := state.snapshots)
          [increment1, armSmallKnown, smallSaved] until branch1
      cil_contract_steps (snapshots := state.snapshots)
        [complementary, carry, armSmallKnown, smallSaved] until carryPath
    · have final : execute 47 [] ready := by
        apply finish ready
        simpa only [result, armSmallResult, show words 0 + word = sum from rfl,
          carry, ite_false] using state
      cil_contract_steps (snapshots := state.snapshots)
        [complementary, carry, armSmallKnown, smallSaved] until final
  have inputLoad (current : Memory) (known : Nat → Option CIL.Value)
      (saved : SmallState program original entered current input output frame known)
      (index : Fin 4) (rest : List Value) :
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address input) :: rest) current =
        .ok (current, .scalar (.i64 (words index)) :: rest) := by
    rw [saved.call.input_field_instruction (by simp) index rest]
    simp only [words, inputLimb,
      call.input_bytes_of_memory_below saved.preserved (reference := input) (by simp)]
  have loadLow := fun pc stack => saved4.snapshots.load (body := armSmallBody profile storage)
    (pc := pc) (args := args) (stack := stack) (.i64 (words 0)) (index := 0) (by rfl)
  cil_contract_steps [args, armSmallArguments, enabled,
    initial.call.input_formed (reference := input) (by simp), saved1.call.input_formed (reference := input) (by simp),
    saved2.call.input_formed (reference := input) (by simp), saved3.call.input_formed (reference := input) (by simp),
    inputLoad _ _ initial 0, inputLoad _ _ saved1 1,
    inputLoad _ _ saved2 2, inputLoad _ _ saved3 3,
    store0, store1, store2, store3, storeSum, storeFlag, loadLow] until arithmetic

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Ordinary valid caller views establish a checked invocation, including every visited running/returned state and the independent arithmetic/overflow result. -/
theorem checked_arm_small_contract (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (enabled : profile.advSimd = true)
    (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method
        (armSmallArguments input output word) memory fuel final returned ∧
      ARMSmallPost memory final returned input output word := by
  let args := armSmallArguments input output word
  obtain ⟨frame, entered, setup, homes, _, _⟩ := arm_small_frame_setup profile storage memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    WP.adequate.mp (arm_small_entry program method storage profile found enabled storageFound
      memory entered input output word frame call setup homes)
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, armSmallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method (armSmallBody profile storage)
      args memory frame entered fuel final returned found checked setup live executed, result⟩

end UInt256Proof.Add.Safety
