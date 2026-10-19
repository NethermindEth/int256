import UInt256.Methods.Add.ARMLanes.Chain
import UInt256.Methods.Add.ARMContract
set_option maxRecDepth 4096

namespace UInt256Proof.Add.ARMLanes

/-- AdvSimd helper whose operand homes hold the right upper, left lower, right lower and left upper halves. -/
def lanesArmBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .v128 0, .v128 0, .v128 0, .v128 0], localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .word64, .word64, .word64, .word64, .word64, .vector128, .vector128, .vector128, .vector128], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .memory .asRef,
  .memory .asRef,
  .arg 1,
  .memory .asRef,
  .memory .asRef,
  .setLocal 0,
  .local 0,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 1,
  .dup,
  .memory .load128,
  .setLocal 2,
  .local 0,
  .memory .load128,
  .setLocal 3,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 4,
  .local 2,
  .local 3,
  .intrinsic (.vector (.add64 128)) 2,
  .local 4,
  .local 1,
  .intrinsic (.vector (.add64 128)) 2,
  .setLocal 5,
  .dup,
  .local 2,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 6,
  .local 5,
  .local 4,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 7,
  .feature .advSimd,
  .brzero 50,
  .intrinsic (.vector (.zero 128)) 0,
  .local 6,
  .const32 1,
  .intrinsic (.advSimd .extract64) 3,
  .setLocal 8,
  .local 6,
  .local 7,
  .const32 1,
  .intrinsic (.advSimd .extract64) 3,
  .setLocal 9,
  .branch 62,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 8,
  .intrinsic (.vector (.sub64 128)) 2,
  .setLocal 10,
  .local 5,
  .local 9,
  .intrinsic (.vector (.sub64 128)) 2,
  .setLocal 11,
  .arg 2,
  .skipInit,
  .feature .advSimd,
  .brzero 82,
  .arg 2,
  .memory .asRef,
  .dup,
  .local 10,
  .memory .store128,
  .const32 1,
  .memory (.add 16 true),
  .local 11,
  .memory .store128,
  .local 10,
  .intrinsic (.vector (.zero 128)) 0,
  .intrinsic (.vector (.eq64 128)) 2,
  .local 8,
  .intrinsic (.vector (.band 128)) 2,
  .setLocal 12,
  .local 11,
  .intrinsic (.vector (.zero 128)) 0,
  .intrinsic (.vector (.eq64 128)) 2,
  .local 9,
  .intrinsic (.vector (.band 128)) 2,
  .setLocal 13,
  .feature .advSimd,
  .brzero 98,
  .arg 3 (some .unsigned8),
  .brzero 102,
  .local 12,
  .local 13,
  .intrinsic (.vector (.bor 128)) 2,
  .branch 106,
  .local 12,
  .local 13,
  .const32 1,
  .intrinsic (.advSimd .extract64) 3,
  .setLocal 14,
  .local 14,
  .intrinsic (.vector (.zero 128)) 0,
  .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero 204,
  .feature .advSimd,
  .brzero 162,
  .arg 3 (some .unsigned8),
  .brnonzero 117,
  .local 14,
  .branch 121,
  .local 12,
  .local 13,
  .const32 1,
  .intrinsic (.advSimd .extract64) 3,
  .setLocal 20,
  .local 11,
  .intrinsic (.vector (.ones 128)) 0,
  .intrinsic (.vector (.eq64 128)) 2,
  .setLocal 21,
  .intrinsic (.vector (.zero 128)) 0,
  .local 21,
  .local 20,
  .intrinsic (.vector (.band 128)) 2,
  .const32 1,
  .intrinsic (.advSimd .extract64) 3,
  .setLocal 22,
  .local 20,
  .local 22,
  .intrinsic (.vector (.bor 128)) 2,
  .setLocal 23,
  .local 7,
  .local 13,
  .local 21,
  .local 23,
  .intrinsic (.vector (.band 128)) 2,
  .intrinsic (.vector (.bor 128)) 2,
  .intrinsic (.vector (.bor 128)) 2,
  .setLocal 7,
  .local 11,
  .local 23,
  .intrinsic (.vector (.sub64 128)) 2,
  .setLocal 11,
  .arg 2,
  .memory .asRef,
  .const32 1,
  .memory (.add 16 true),
  .local 11,
  .memory .store128,
  .local 7,
  .const32 1,
  .intrinsic (.vector (.extract64 128)) 2,
  .const32 0,
  .convI8,
  .gtu,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .feature .advSimd,
  .brnonzero 215,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 7,
  .const32 1,
  .intrinsic (.vector (.extract64 128)) 2,
  .const32 0,
  .convI8,
  .gtu,
  .ret (some .unsigned8)] }

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
theorem lanes_arm_helper_checked_with_flag (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true)
    (program : CIL.Program) (method : Nat) (found : program[method]? = some (lanesArmBody profile))
    (memory : Memory) (left right output : Reference) (flag : BitVec 32)
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      CIL.NarrowKind.unsigned8.extend returned = returned ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let b := lanesArmBody profile
  have disabledFalse (disabled : b.profile.advSimd = false) : False := by
    change profile.advSimd = false at disabled
    rw [enabled] at disabled
    contradiction
  apply checked_lanes_arm_contract_with_flag program b method armSpecs found
    (b.code.drop 37) (b.code.drop 62) (b.code.take 62) (b.code.drop 69)
    rfl rfl
    rfl rfl armSpecs_first (fun disabled => (disabledFalse disabled).elim) (fun disabled => (disabledFalse disabled).elim)
    (b.code.take 69) (b.code.drop 82) rfl (by simp only [b, lanesArmBody, earlyOutputCode, enabled, ite_true]; rfl)
    (b.code.take 82) (b.code.drop 94) rfl rfl
    (b.code.take 94) (b.code.drop 111) rfl (by simp only [b, lanesArmBody, decisionCode, enabled, ite_true]; rfl)
    (b.code.take 204) (b.code.drop 222) rfl (by simp only [b, lanesArmBody, fastOutputCode, enabled, ite_true]; rfl) rfl
    (b.code.take 111) (b.code.drop 113) rfl rfl
    (b.code.take 113) (b.code.drop 162) rfl rfl armSpecs_repair ⟨rfl,rfl⟩ rfl rfl enabled
    memory left right output flag flagFit call

#print axioms lanes_arm_helper_checked_with_flag
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
/-- The actual scalar dispatcher's vector call and forwarding return use the independently certified helper and its proved scalar result shape. -/
theorem lanes_arm_parent_call (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (vectorFound : program[vectorIndex]? = some (lanesArmBody profile)) (enabled : profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (post : Memory → List Value → Prop)
    (continuation : ∀ childFuel final returnedFlag,
      InvocationCertificate program vectorIndex (vector128Arguments left right output flag)
        memory childFuel
        final [.scalar (.i32 returnedFlag)] →
      inputValue final output = inputValue memory left + inputValue memory right →
      (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) →
      access final output 32 1 true = .ok () →
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) →
      post (leaveFrame frame final) [.scalar (.i32 returnedFlag)]) :
    ∃ fuel final returned,
      run program fuel method 25 (vector128Arguments left right output flag)
        frame [] memory = .ok (final, returned) ∧ post final returned := by
    obtain ⟨childFuel, final, returnedFlag, certified, result, returnedFit, overflow, writable, footprint⟩ :=
      lanes_arm_helper_checked_with_flag profile enabled program vectorIndex vectorFound memory left right output flag flagFit call
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    have fetched : (armScalarBody profile vectorIndex smallIndex).code[29]? = some (.call vectorIndex 4) := by rfl
    have stepped : step (armScalarBody profile vectorIndex smallIndex) (.call vectorIndex 4) 29
        (vector128Arguments left right output flag) frame
        [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (.call vectorIndex (vector128Arguments left right output flag) [] memory) := by
      simp [step, flagFit, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have returned : run program 1 method 30
        (vector128Arguments left right output flag) frame [.scalar (.i32 returnedFlag)] final =
        .ok (leaveFrame frame final, [.scalar (.i32 returnedFlag)]) := by
      simp [run, found, armScalarBody, step, returnedFit, List.mapM, Option.bind, checkedValue, numericValue, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      rfl
    obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨_, certified.1⟩ ⟨1, returned⟩
    have done := continuation childFuel final returnedFlag certified result overflow writable footprint
    have finish : ∃ fuel final returned,
        run program fuel method 29 (vector128Arguments left right output flag)
          frame [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
          .ok (final, returned) ∧ post final returned := ⟨fuel, _, _, executed, done⟩
    repeat' first
      | exact finish
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, flagFit, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms lanes_arm_parent_call
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety
/-- Complete the small route from its saved arguments, certified helper call, scalar forwarding return and parent retirement. -/
theorem lanes_arm_scalar_small_finish (program : CIL.Program) (method vectorIndex smallIndex storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (vectorFound : program[vectorIndex]? = some (lanesArmBody profile)) (smallFound : program[smallIndex]? = some (armSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (enabled : profile.advSimd = true)
    (original current : Memory) (frame : Frame) (args : List Value)
    (left right output source home : Reference) (word : BitVec 64) (flag : BitVec 32)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [source] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (root : frame.locals[7]? = some (.root (some (.address source))))
    (slot : frame.locals[8]? = some (.bytes .word64 home))
    (loaded : read current home 8 1 = .ok (numberBytes word.toNat 8))
    (outputArg : args[2]? = some (.reference (.address output)))
    (sum : inputValue current source + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right)
    (naturalSum : (inputValue current source).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) :
    ∃ fuel final returned,
      run program fuel method 36 args frame [] current = .ok (final, returned) ∧
      ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  apply arm_scalar_small_arguments program method vectorIndex smallIndex profile found enabled current frame args source output home word root slot loaded
    (currentCall.input_formed (by simp)) outputArg (currentCall.output_formed (by simp)) post
  apply arm_small_parent_call program method vectorIndex smallIndex storage profile found smallFound storageFound enabled current source output word frame args currentCall post
  intro childFuel final returned certified result
  refine ⟨arm_scalar_retire original current final frame left right output returned call preserved next owned
    result.wellFormed (result.value.trans sum) ⟨_, result.flag⟩ result.writable result.footprint, ?_⟩
  intro _
  simpa only [naturalSum] using result.flag

#print axioms lanes_arm_scalar_small_finish
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety
/-- The vector route yields the same wrapping postcondition after parent retirement. -/
theorem lanes_arm_scalar_vector_finish (program : CIL.Program) (method vectorIndex smallIndex storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (vectorFound : program[vectorIndex]? = some (lanesArmBody profile)) (smallFound : program[smallIndex]? = some (armSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (enabled : profile.advSimd = true)
    (original current : Memory) (frame : Frame) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 25 (vector128Arguments left right output flag)
        frame [] current = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  apply lanes_arm_parent_call program method vectorIndex smallIndex profile found vectorFound enabled current left right output flag flagFit frame currentCall post
  intro childFuel final returnedFlag certified result overflow writable footprint
  have wellFormed := invoke_preserves_wellFormed _ _ _ _ _ _ _ currentCall.1.1 certified.1
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  rw [keptLeft, keptRight] at result
  refine ⟨arm_scalar_retire original current final frame left right output [.scalar (.i32 returnedFlag)]
    call preserved next owned wellFormed result ⟨returnedFlag, rfl⟩ writable
    (fun id old offset untouched => footprint id offset old untouched), ?_⟩
  intro reporting
  have exactFlag := overflow reporting
  rw [keptLeft, keptRight] at exactFlag
  rw [exactFlag]

#print axioms lanes_arm_scalar_vector_finish
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety
/-- Complete ARM scalar dispatcher execution, including both small-operand routes and the vector route. -/
theorem lanes_arm_scalar_entry (program : CIL.Program) (method vectorIndex smallIndex storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (vectorFound : program[vectorIndex]? = some (lanesArmBody profile)) (smallFound : program[smallIndex]? = some (armSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (enabled : profile.advSimd = true)
    (original entered : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (frame : Frame)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (armScalarBody profile vectorIndex smallIndex) (vector128Arguments left right output flag) original =
      .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity armScalarLocalSpecs frame.locals) :
    ∃ fuel final returned,
      run program fuel method 0 (vector128Arguments left right output flag)
        frame [] entered = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let args := vector128Arguments left right output flag
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  have enteredCall := call.after_frame_setup setup
  have setupPreserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have enteredWF := enteredCall.1.1
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ source id, id ∈ (armScalarSavedFrame frame source).owned → original.nextIdentity ≤ id :=
    fun _ id member => (fresh.2 id member).1
  have rootSlot := (arm_scalar_slots program method vectorIndex smallIndex profile found enabled entered original.nextIdentity frame homes).1
  have root : ∀ source, (armScalarSavedFrame frame source).locals[7]? =
      some (.root (some (.address source))) := by
    intro source
    simp only [armScalarSavedFrame, List.getElem?_set_self', rootSlot]
    rfl
  have wordSlot : ∀ source home, frame.locals[8]? = some (.bytes .word64 home) →
      (armScalarSavedFrame frame source).locals[8]? = some (.bytes .word64 home) := by
    intro source home slot
    simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot
  apply arm_scalar_dispatch_prefix program method vectorIndex smallIndex profile found enabled original.nextIdentity entered [left, right] [output]
    frame args left right enteredCall enteredWF homes (by simp) (by simp) rfl rfl post
  intro home current slot loaded preserved currentCall authority
  have originalPreserved := setupPreserved.trans preserved
  have next := arm_scalar_watermark original entered current frame homes enteredWF currentCall.1.1 authority
  by_cases rightSmall : armScalarUpper current right = BitVec.ofNat 64 0
  · simp only [armScalarTarget, rightSmall, ite_true]
    have lowKept : inputLimb entered right 0 = inputLimb current right 0 := by
      simp only [inputLimb,
        call.input_bytes_of_memory_below setupPreserved (reference := right) (by simp),
        call.input_bytes_of_memory_below originalPreserved (reference := right) (by simp)]
    rw [lowKept] at loaded
    exact lanes_arm_scalar_small_finish program method vectorIndex smallIndex storage profile found vectorFound smallFound storageFound enabled original current (armScalarSavedFrame frame left) args
      left right output left home (inputLimb current right 0) flag call
      (arm_scalar_select_input program current [left, right] left output currentCall (by simp))
      originalPreserved next (owned left) (root left) (wordSlot left home slot) loaded rfl
      (arm_scalar_small_values program false original current left right output call originalPreserved rightSmall).1
      (arm_scalar_small_values program false original current left right output call originalPreserved rightSmall).2
  · by_cases leftSmall : armScalarUpper current left = BitVec.ofNat 64 0
    · simp only [armScalarTarget, rightSmall, leftSmall, ite_false, ite_true]
      apply arm_scalar_swap_prefix program method vectorIndex smallIndex profile found enabled original.nextIdentity entered current [left, right] [output]
        frame args left right currentCall enteredWF homes authority (by simp) (by simp) rfl rfl post
      intro swappedHome after swappedSlot swappedRead afterPreserved afterCall afterAuthority
      have allPreserved := originalPreserved.trans afterPreserved
      have afterNext := arm_scalar_watermark original entered after frame homes enteredWF afterCall.1.1 afterAuthority
      have rightKept : inputValue after right = inputValue current right := by
        simp only [inputValue,
          call.input_bytes_of_memory_below allPreserved (reference := right) (by simp),
          call.input_bytes_of_memory_below originalPreserved (reference := right) (by simp)]
      have sums := arm_scalar_small_values program true original current left right output call originalPreserved leftSmall
      apply lanes_arm_scalar_small_finish program method vectorIndex smallIndex storage profile found vectorFound smallFound storageFound enabled original after (armScalarSavedFrame frame right) args
        left right output right swappedHome (inputLimb current left 0) flag call
        (arm_scalar_select_input program after [left, right] right output afterCall (by simp))
        allPreserved afterNext (owned right) (root right) (wordSlot right swappedHome swappedSlot) swappedRead rfl
      · simpa only [rightKept, ite_true] using sums.1
      · simpa only [rightKept, ite_true] using sums.2
    · simp only [armScalarTarget, rightSmall, leftSmall, ite_false]
      exact lanes_arm_scalar_vector_finish program method vectorIndex smallIndex storage profile found vectorFound smallFound storageFound enabled original current (armScalarSavedFrame frame left)
        left right output flag flagFit call currentCall originalPreserved next (owned left)

#print axioms lanes_arm_scalar_entry
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety
/-- Certify the complete ARM dispatcher and all visited states from ordinary caller views. -/
theorem lanes_checked_arm_scalar_contract (program : CIL.Program) (method vectorIndex smallIndex storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (vectorFound : program[vectorIndex]? = some (lanesArmBody profile)) (smallFound : program[smallIndex]? = some (armSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (enabled : profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method
        (vector128Arguments left right output flag) memory fuel final returned ∧
      ARMScalarReportingPost memory final returned left right output flag := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, setup, homes, _, _⟩ := arm_scalar_frame_setup profile vectorIndex smallIndex memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    lanes_arm_scalar_entry program method vectorIndex smallIndex storage profile found vectorFound smallFound storageFound enabled memory entered left right output flag flagFit frame call setup homes
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method (armScalarBody profile vectorIndex smallIndex)
      args memory frame entered fuel final returned found checked setup live executed, result⟩

#print axioms lanes_checked_arm_scalar_contract
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety
theorem lanes_checked_arm_add_contract (program : CIL.Program) (entry scalar vector small storage : Nat)
    (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true) (disabled : profile.avx2 = false)
    (entryFound : program[entry]? = some (publicScalarBody profile scalar))
    (scalarFound : program[scalar]? = some (armScalarBody profile vector small))
    (vectorFound : program[vector]? = some (lanesArmBody profile))
    (smallFound : program[small]? = some (armSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    WrappingBinaryContract (· + ·) program entry := by
  apply add_contract_of_scalar program entry scalar profile entryFound disabled
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    lanes_checked_arm_scalar_contract program scalar vector small storage profile scalarFound vectorFound smallFound storageFound enabled
      memory left right output 0 rfl call

#print axioms lanes_checked_arm_add_contract
end

end UInt256Proof.Add.ARMLanes
