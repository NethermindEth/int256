import UInt256.Methods.Add.ARMSmallState
import UInt256.Methods.Add.InputWords
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

/-- Limbs stored through StoreLimbs that are the small-sum result leave the exact sum, the
    overflow bit and the caller footprint once the frame is retired. -/
theorem ARMSmallPost.of_stored {program : CIL.Program} {original entered current stored : Memory}
    {input output : Reference} {word second third fourth : BitVec 64} {flag : BitVec 32}
    {frame : Frame} {body : CIL.Method} {args : List Value}
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame body args original = .ok (frame, entered))
    (preserved : MemoryBelow original.nextIdentity original current)
    (valid : CallingConditions program stored [input] [output])
    (outside : ∀ id offset, OutsideOutput output id offset →
      stored.cells id offset = current.cells id offset)
    (value : inputValue stored output = BitVec.ofNat 256
      ((inputLimb original input 0 + word).toNat + second.toNat * 2^64 + third.toNat * 2^128 +
        fourth.toNat * 2^192))
    (agrees : (armSmallResult (inputLimb original input) word).1 1 = second ∧
      (armSmallResult (inputLimb original input) word).1 2 = third ∧
      (armSmallResult (inputLimb original input) word).1 3 = fourth ∧
      (armSmallResult (inputLimb original input) word).2 = flag) :
    ARMSmallPost original (leaveFrame frame stored) [.scalar (.i32 flag)] input output word := by
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retired := leaveFrame_preserves_memory_below frame stored original.nextIdentity
    (fun id member => (fresh.2 id member).1)
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retired.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have mathematical := arm_small_result_value original input word
    simp only [UInt256Model.value, armSmallOutputWords, agrees] at mathematical
    simpa only [inputValue, bytes] using value.trans mathematical
  · have initial : UInt256Model.value (inputLimb original input) = inputValue original input :=
      UInt256Proof.input_value (fun offset => (original.cells input.allocation offset).bits)
        input.offset
    rw [← agrees.2.2.2, arm_small_result_flag, initial]
  · exact (retired.access output outputOld 32 1 true).trans
      (valid.1.writable (wordView output) (by simp))
  · intro id old offset untouched
    exact (retired.cells id old offset).trans
      ((outside id offset untouched).trans (preserved.cells id old offset))

/-- Store the output limbs through StoreLimbs and return the remembered byte flag: limbs and
    flag that are the small-sum result give the exact sum, overflow bit and caller footprint. -/
theorem arm_small_exit (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (original entered current : Memory) (input output : Reference) (word : BitVec 64)
    (frame : Frame) (call : CallingConditions program original [input] [output])
    (setup : enterFrame (armSmallBody profile storage) (armSmallArguments input output word)
      original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (currentCall : CallingConditions program current [input] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (known : Nat → Option CIL.Value) (snapshots : LocalSnapshots current frame.locals known)
    (second third fourth : BitVec 64) (flag : BitVec 32) (flagKnown : known 6 = some (.i32 flag))
    (agrees : (armSmallResult (inputLimb original input) word).1 1 = second ∧
      (armSmallResult (inputLimb original input) word).1 2 = third ∧
      (armSmallResult (inputLimb original input) word).1 3 = fourth ∧
      (armSmallResult (inputLimb original input) word).2 = flag) :
    WP (Execution (fun fuel => run program fuel method 52
        (armSmallArguments input output word) frame
        [.scalar (.i64 fourth), .scalar (.i64 third), .scalar (.i64 second),
          .scalar (.i64 (inputLimb original input 0 + word)), .reference (.address output)]
        current))
      (fun result => ARMSmallPost original result.1 result.2 input output word) := by
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract profile program storage
      storageFound current [input] output (inputLimb original input 0 + word) second third fourth
      currentCall
  have formed := currentCall.output_formed (by simp : output ∈ [output])
  have stepped : step (armSmallBody profile storage) (.call storage 5) 52
      (armSmallArguments input output word) frame
      [.scalar (.i64 fourth), .scalar (.i64 third), .scalar (.i64 second),
        .scalar (.i64 (inputLimb original input 0 + word)), .reference (.address output)]
      current = .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output
        (inputLimb original input 0 + word) second third fourth) [] current) := by
    cil_checked_step [UInt256Proof.Multiply.LimbStorage.arguments, formed]
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have retained := snapshots.after_unchanged currentCall.1.1 authority (by
    intro index loaded kind home _ slot offset _
    exact outside _ _ (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le (call.1.1.1 _ _ present).1
      (homes.home_bound index kind home slot)))))
  have flagFit : CIL.NarrowKind.unsigned8.extend flag = flag := by
    rw [← agrees.2.2.2, arm_small_result_flag]
    split <;> rfl
  apply WP.call (helperPost := fun result => result.1 = stored ∧ result.2 = [])
    found (by rfl) stepped ⟨childFuel, (stored, []), invoked, rfl, rfl⟩
  rintro final values ⟨rfl, rfl⟩
  cil_contract_steps (snapshots := retained) [found, flagKnown, flagFit]
  exact ARMSmallPost.of_stored call setup preserved valid outside value agrees

/-- Full extracted ARM helper execution: input snapshots, low sum, every carry path and the
    shared postcondition. -/
theorem arm_small_entry (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage))
    (enabled : profile.advSimd = true)
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (armSmallBody profile storage) (armSmallArguments input output word)
      original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    WP (Execution (fun fuel => run program fuel method 0
      (armSmallArguments input output word) frame [] entered))
      (fun result => ARMSmallPost original result.1 result.2 input output word) := by
  have enteredCall := call.after_frame_setup setup
  have valid := enteredCall.1
  have world := enteredCall.2
  have enteredFormed := valid.1
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have snapshots := LocalSnapshots.empty entered frame.locals
  have limbs := fun current below =>
    call.input_words_kept (current := current) below input (by simp)
  have exit := fun current => arm_small_exit program method storage profile found storageFound
    original entered current input output word frame call setup homes
  cil_contract_steps (snapshots := snapshots)
    [found, armSmallArguments, enabled, limbs _ preserved]
  split
  next low =>
    have carry := BitVec.not_lt.mpr low
    cil_contract_steps (snapshots := localSnapshots_5) [found, armSmallArguments]
    exact WP.adequate.mp (exit storedLocal_5 ⟨valid, by stored_world⟩ preserved _
      localSnapshots_5 _ _ _ _ (by rfl) (by simp [armSmallResult, carry]))
  next carry =>
    replace carry := BitVec.not_le.mp carry
    cil_contract_steps (snapshots := localSnapshots_5) [found, armSmallArguments]
    have lastIndex : (3 : Fin 4).val = 3 := rfl
    split
    next first =>
      cil_contract_steps (snapshots := localSnapshots_6) [found, armSmallArguments]
      exact WP.adequate.mp (exit storedLocal_6 ⟨valid, by stored_world⟩ preserved _
        localSnapshots_6 _ _ _ _ (by rfl) (by
          simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, lastIndex]))
    next first =>
      replace first := Decidable.not_not.mp first
      cil_contract_steps (snapshots := localSnapshots_6) [found, armSmallArguments]
      split
      next second =>
        cil_contract_steps (snapshots := localSnapshots_7) [found, armSmallArguments]
        exact WP.adequate.mp (exit storedLocal_7 ⟨valid, by stored_world⟩ preserved _
          localSnapshots_7 _ _ _ _ (by rfl) (by
            simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second,
              lastIndex]))
      next second =>
        replace second := Decidable.not_not.mp second
        cil_contract_steps (snapshots := localSnapshots_7) [found, armSmallArguments]
        exact WP.adequate.mp (exit storedLocal_9 ⟨valid, by stored_world⟩ preserved _
          localSnapshots_9 _ _ _ _ (by rfl) (by
            simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second,
              lastIndex]
            split <;> rfl))

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
