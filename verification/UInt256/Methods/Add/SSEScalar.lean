import UInt256.Methods.Add.SSEEntry
import UInt256.Methods.Add.PortableSmall
import UInt256.Methods.Add.ARMScalarEntry

namespace UInt256Proof.Add.Safety

open CIL.Safety UInt256Model.Safety

-- AddScalar with AdvSimd disabled: right-small, left-small, then the SSE4.2 vector helper.
def sseScalarBody (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .nullRef, .i64 0], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .word64, .reference, .word64], parameterHomes := [], staticSites := [], code := [
  .feature .advSimd,
  .brzero 41,
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
  .arg 1,
  .fieldAt 0 8,
  .setLocal 0,
  .arg 1,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 16 8,
  .bor,
  .arg 1,
  .fieldAt 24 8,
  .bor,
  .brnonzero 58,
  .arg 0,
  .local 0,
  .arg 2,
  .call smallIndex 3,
  .ret (some .unsigned8),
  .arg 0,
  .fieldAt 0 8,
  .setLocal 1,
  .arg 0,
  .fieldAt 8 8,
  .arg 0,
  .fieldAt 16 8,
  .bor,
  .arg 0,
  .fieldAt 24 8,
  .bor,
  .brnonzero 75,
  .arg 1,
  .local 1,
  .arg 2,
  .call smallIndex 3,
  .ret (some .unsigned8),
  .feature .sse42,
  .brzero 83,
  .arg 0,
  .arg 1,
  .arg 2,
  .arg 3 (some .unsigned8),
  .call vectorIndex 4,
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
  .unsupported "Unreachable under selected profile"] }

theorem sse_scalar_frame_setup (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame (sseScalarBody profile vectorIndex smallIndex) args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity armScalarLocalSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨slots, owned, result, made, homes⟩ := make_word_locals memory memory.nextIdentity armScalarLocalSpecs wellFormed
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have metadata : (sseScalarBody profile vectorIndex smallIndex).localKinds = wordKinds armScalarLocalSpecs ∧
      (sseScalarBody profile vectorIndex smallIndex).locals = wordInitializers armScalarLocalSpecs := by
    simp [armScalarLocalSpecs, wordKinds, wordInitializers, sseScalarBody]
  have entered : enterFrame (sseScalarBody profile vectorIndex smallIndex) args memory = .ok (frame, result) := by
    unfold enterFrame
    dsimp only
    rw [metadata.1, metadata.2, made]
    simp only [Bind.bind, Except.bind, sseScalarBody, makeArgumentHomes, makeParameterHomes, Pure.pure, Except.pure, List.map_nil, List.append_nil]
    rfl
  exact ⟨frame, result, entered, homes, enterFrame_preserves_caller_memory _ _ _ _ _ entered,
    enterFrame_preserves_wellFormed _ _ _ _ _ wellFormed entered⟩

/-- The disabled AdvSimd guard jumps straight to the portable small-operand tests. -/
theorem sse_scalar_dispatch (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex)) (disabled : profile.advSimd = false)
    (memory : Memory) (frame : Frame) (args : List Value) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method 41 args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] memory = .ok (final, returned) ∧ post final returned := by
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, sseScalarBody, disabled, pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

def sseSaveStart (swapped : Bool) : Nat := if swapped then 58 else 41

/-- Save the selected operand's low limb in its private word home (right in local0, left in local1). -/
theorem sse_scalar_save_low (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (swapped : Bool) (boundary : Nat) (entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (input : Reference)
    (call : CallingConditions program current inputs outputs) (member : input ∈ inputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary armScalarLocalSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[if swapped then 0 else 1]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ home after,
      frame.locals[if swapped then 1 else 0]? = some (.bytes .word64 home) →
      read after home 8 1 = .ok (numberBytes (inputLimb current input 0).toNat 8) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run program fuel method (sseSaveStart swapped + 3) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (sseSaveStart swapped) args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨home, slot, bound, _, writable⟩ := homes.word_at (if swapped then 1 else 0) (BitVec.ofNat 64 0)
    (by cases swapped <;> rfl)
  obtain ⟨after, loaded, preserved, afterCall, afterAuthority, _, stored⟩ :=
    checked_numeric_home_store program (sseScalarBody profile vectorIndex smallIndex)
      boundary entered current inputs outputs frame call enteredWF authority (if swapped then 1 else 0)
      ⟨.word64, .i64 0, 0, rfl⟩ home slot bound writable (.i64 (inputLimb current input 0)) (inputLimb current input 0).toNat rfl
  have done := continuation home after slot loaded preserved afterCall afterAuthority
  have formed := call.input_formed member
  have field := call.input_field_instruction member 0
  dsimp at field
  cases swapped <;> simp only [sseSaveStart, Bool.false_eq_true, ite_false, ite_true] at argument slot stored done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, formValue, formed, field, pureArity,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- The three upper limbs of the selected operand are or-combined from checked field loads. -/
theorem sse_scalar_upper_loads (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (swapped : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (inputs outputs : List Reference) (input : Reference)
    (call : CallingConditions program memory inputs outputs) (member : input ∈ inputs)
    (argument : args[if swapped then 0 else 1]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (sseSaveStart swapped + 11)
        args frame [.scalar (.i64 (armScalarUpper memory input))] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (sseSaveStart swapped + 3)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
    have formed := call.input_formed member
    have loaded := call.input_field_instruction member
    have l1 := loaded 1
    have l2 := loaded 2
    have l3 := loaded 3
    dsimp at l1 l2 l3
    simp only [show (3 : Fin 4).val = 3 from rfl] at l3
    unfold armScalarUpper at continuation
    cases swapped <;> simp only [sseSaveStart, Bool.false_eq_true, ite_false, ite_true] at argument continuation ⊢
    all_goals
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, numericValue, formValue, formed, l1, l2, l3, pureArity,
               scalars, CIL.step.eq_def, CIL.truth, CIL.binary,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- A zero upper part selects the small helper; otherwise control continues to the next test. -/
theorem sse_scalar_upper_branch (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (swapped : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (condition : BitVec 64) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method
        (if condition = BitVec.ofNat 64 0 then sseSaveStart swapped + 12 else sseSaveStart swapped + 17)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (sseSaveStart swapped + 11)
        args frame [.scalar (.i64 condition)] memory = .ok (final, returned) ∧ post final returned := by
    cases swapped <;> by_cases zero : condition = BitVec.ofNat 64 0
    all_goals
      simp only [sseSaveStart, Bool.false_eq_true, ite_false, ite_true, zero] at continuation ⊢
      apply run_next_exists post found (by rfl) _ continuation
      simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth,
        show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, zero,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms sse_scalar_frame_setup
#print axioms sse_scalar_dispatch
#print axioms sse_scalar_save_low
#print axioms sse_scalar_upper_loads
#print axioms sse_scalar_upper_branch
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Caller guarantees of the SSE vector helper invoked by the scalar dispatcher. -/
def SSEHelperContract (program : CIL.Program) (vectorIndex : Nat) : Prop :=
  ∀ (memory : Memory) (left right output : Reference) (flag : BitVec 32),
    CIL.NarrowKind.unsigned8.extend flag = flag →
    CallingConditions program memory [left, right] [output] →
    ∃ fuel final returned,
      InvocationCertificate program vectorIndex (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      CIL.NarrowKind.unsigned8.extend returned = returned ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset)

/-- Caller guarantees of the portable small-operand helper. -/
def PortableSmallContract (program : CIL.Program) (smallIndex : Nat) : Prop :=
  ∀ (memory : Memory) (input output : Reference) (word : BitVec 64),
    CallingConditions program memory [input] [output] →
    ∃ fuel final returned,
      InvocationCertificate program smallIndex (armSmallArguments input output word) memory fuel final returned ∧
      ARMSmallPost memory final returned input output word

/-- The extracted SSE helper body meets the helper contract. -/
theorem sse_helper_contract (profile : CIL.FeatureProfile) (disabled : profile.advSimd = false)
    (sse2 : profile.sse2 = true) (ssse3 : profile.ssse3 = true)
    (program : CIL.Program) (vectorIndex carry storage : Nat)
    (vectorFound : program[vectorIndex]? = some (sseBody profile carry storage))
    (carryFound : program[carry]? = some (UInt256Proof.Add.CarrySafety.carryBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    SSEHelperContract program vectorIndex := fun memory left right output flag flagFit call =>
  sse_helper_checked profile disabled sse2 ssse3 program vectorIndex carry storage vectorFound carryFound storageFound
    memory left right output flag flagFit call

/-- The extracted portable small body meets the small-helper contract. -/
theorem portable_small_contract (program : CIL.Program) (smallIndex storage : Nat) (profile : CIL.FeatureProfile)
    (smallFound : program[smallIndex]? = some (portableSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (disabled : profile.advSimd = false) : PortableSmallContract program smallIndex :=
  fun memory input output word call =>
    checked_portable_small_contract program smallIndex storage profile smallFound storageFound disabled memory input output word call

#print axioms sse_helper_contract
#print axioms portable_small_contract
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- The selected small route calls the certified portable helper and forwards its byte flag. -/
theorem sse_scalar_small_call (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex)) (smallContract : PortableSmallContract program smallIndex)
    (swapped : Bool) (memory : Memory) (frame : Frame) (args : List Value) (source output home : Reference) (word : BitVec 64)
    (slot : frame.locals[if swapped then 1 else 0]? = some (.bytes .word64 home))
    (loaded : read memory home 8 1 = .ok (numberBytes word.toNat 8))
    (sourceArg : args[if swapped then 1 else 0]? = some (.reference (.address source)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program memory [source] [output])
    (post : Memory → List Value → Prop)
    (continuation : ∀ childFuel final returned,
      InvocationCertificate program smallIndex
        (armSmallArguments source output word) memory childFuel final returned →
      ARMSmallPost memory final returned source output word →
      post (leaveFrame frame final) returned) :
    ∃ fuel final returned,
      run program fuel method (sseSaveStart swapped + 12) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨childFuel, final, returned, certified, result⟩ :=
    smallContract memory source output word call
  have fi := call.input_formed (reference := source) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have stepped : ∀ pc, step (sseScalarBody profile vectorIndex smallIndex) (.call smallIndex 3) pc args frame
      [.reference (.address output), .scalar (.i64 word), .reference (.address source)] memory =
        .ok (.call smallIndex (armSmallArguments source output word) [] memory) := by
    intro pc
    simp [step, armSmallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have wordLoad := fun (pc : Nat) (stack : List Value) => step_load_word64
    (body := sseScalarBody profile vectorIndex smallIndex) (pc := pc) (args := args) (stack := stack) slot loaded
  have done := continuation childFuel final returned certified result
  cases swapped <;> simp only [sseSaveStart, Bool.false_eq_true, ite_false, ite_true] at slot sourceArg wordLoad ⊢
  all_goals
    have returnedRun : ∀ pc, (sseScalarBody profile vectorIndex smallIndex).code[pc]? = some (.ret (some .unsigned8)) →
        run program 1 method pc args frame (returned ++ []) final = .ok (leaveFrame frame final, returned) := by
      intro pc fetched
      have returns : (sseScalarBody profile vectorIndex smallIndex).returnsValue = true := rfl
      rw [result.flag]
      split <;> simp [run, found, fetched, returns, step, checkedValue, numericValue, List.mapM, List.mapM.loop, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      all_goals rfl
    repeat' first
      | exact (let ⟨fuel, executed⟩ := run_call_exists found (by rfl) (stepped _) ⟨childFuel, certified.1⟩ ⟨1, returnedRun _ (by rfl)⟩
          ⟨fuel, leaveFrame frame final, returned, executed, done⟩)
      | (apply run_next_exists post found (by rfl)
         first
         | exact wordLoad _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, sourceArg, outputArg, checkedValue, formValue, fi, fo,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- The small route reaches the shared scalar reporting postcondition for either operand order. -/
theorem sse_scalar_small_finish (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex)) (smallContract : PortableSmallContract program smallIndex)
    (swapped : Bool) (original current : Memory) (frame : Frame)
    (left right output home : Reference) (flag : BitVec 32)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (slot : frame.locals[if swapped then 1 else 0]? = some (.bytes .word64 home))
    (loaded : read current home 8 1 = .ok (numberBytes (inputLimb current (if swapped then left else right) 0).toNat 8))
    (small : armScalarUpper current (if swapped then left else right) = BitVec.ofNat 64 0) :
    ∃ fuel final returned,
      run program fuel method (sseSaveStart swapped + 12) (vector128Arguments left right output flag) frame [] current =
        .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  have sums := arm_scalar_small_values program swapped original current left right output call preserved small
  apply sse_scalar_small_call program method vectorIndex smallIndex profile found smallContract swapped current frame
    (vector128Arguments left right output flag) (if swapped then right else left) output home _ slot loaded
    (by cases swapped <;> rfl) rfl
    (arm_scalar_select_input program current [left, right] _ output currentCall (by cases swapped <;> simp))
  intro childFuel final returned certified result
  refine ⟨arm_scalar_retire original current final frame left right output returned call preserved next owned
    result.wellFormed (result.value.trans sums.1) ⟨_, result.flag⟩ result.writable result.footprint, ?_⟩
  intro _
  simpa only [sums.2] using result.flag

/-- With SSE4.2 enabled the dispatcher calls the certified vector helper and forwards its flag. -/
theorem sse_scalar_vector_finish (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (helper : SSEHelperContract program vectorIndex) (sse42 : profile.sse42 = true)
    (original current : Memory) (frame : Frame) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 75 (vector128Arguments left right output flag)
        frame [] current = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  obtain ⟨childFuel, final, returnedFlag, certified, result, returnedFit, overflow, writable, footprint⟩ :=
    helper current left right output flag flagFit currentCall
  have fl := currentCall.input_formed (reference := left) (by simp)
  have fr := currentCall.input_formed (reference := right) (by simp)
  have fo := currentCall.output_formed (reference := output) (by simp)
  have stepped : step (sseScalarBody profile vectorIndex smallIndex) (.call vectorIndex 4) 81
      (vector128Arguments left right output flag) frame
      [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] current =
      .ok (.call vectorIndex (vector128Arguments left right output flag) [] current) := by
    simp [step, flagFit, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned : run program 1 method 82
      (vector128Arguments left right output flag) frame [.scalar (.i32 returnedFlag)] final =
      .ok (leaveFrame frame final, [.scalar (.i32 returnedFlag)]) := by
    simp [run, found, sseScalarBody, step, returnedFit, List.mapM, List.mapM.loop, Option.bind, checkedValue, numericValue, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    try rfl
  obtain ⟨fuel, executed⟩ := run_call_exists found (by rfl) stepped ⟨_, certified.1⟩ ⟨1, returned⟩
  have wellFormed := invoke_preserves_wellFormed _ _ _ _ _ _ _ currentCall.1.1 certified.1
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  rw [keptLeft, keptRight] at result
  have done : post (leaveFrame frame final) [.scalar (.i32 returnedFlag)] := by
    refine ⟨arm_scalar_retire original current final frame left right output [.scalar (.i32 returnedFlag)]
      call preserved next owned wellFormed result ⟨returnedFlag, rfl⟩ writable
      (fun id old offset untouched => footprint id offset old untouched), ?_⟩
    intro reporting
    have exactFlag := overflow reporting
    rw [keptLeft, keptRight] at exactFlag
    rw [exactFlag]
  have finish : ∃ fuel final returned,
      run program fuel method 81 (vector128Arguments left right output flag)
        frame [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] current =
        .ok (final, returned) ∧ post final returned := ⟨fuel, _, _, executed, done⟩
  have bodyProfile : (sseScalarBody profile vectorIndex smallIndex).profile = profile := rfl
  repeat' first
    | exact finish
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, flagFit, sse42, bodyProfile, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo, pureArity, scalars,
           CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms sse_scalar_small_call
#print axioms sse_scalar_small_finish
#print axioms sse_scalar_vector_finish
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem sse_input_limb_kept {program : CIL.Program} {original current : Memory} {left right output input : Reference}
    (call : CallingConditions program original [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current) (member : input ∈ [left, right]) :
    inputLimb current input = inputLimb original input := by
  funext i
  simp only [inputLimb, call.input_bytes_of_memory_below preserved member]

/-- Complete SSE dispatcher execution: both small-operand routes and the SSE4.2 vector route. -/
theorem sse_scalar_entry (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (helper : SSEHelperContract program vectorIndex) (small : PortableSmallContract program smallIndex)
    (disabled : profile.advSimd = false) (sse42 : profile.sse42 = true)
    (original entered : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (frame : Frame)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (sseScalarBody profile vectorIndex smallIndex) (vector128Arguments left right output flag) original =
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
  have owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  apply sse_scalar_dispatch program method vectorIndex smallIndex profile found disabled entered frame args post
  apply sse_scalar_save_low program method vectorIndex smallIndex profile found false original.nextIdentity entered entered
    [left, right] [output] frame args right enteredCall (by simp) enteredWF homes
    (MemoryBelow.refl _ _).accessBelow rfl post
  intro home after slot loaded preserved afterCall authority
  have afterPreserved := setupPreserved.trans preserved
  have afterNext := arm_scalar_watermark original entered after frame homes enteredWF afterCall.1.1 authority
  apply sse_scalar_upper_loads program method vectorIndex smallIndex profile found false after frame args
    [left, right] [output] right afterCall (by simp) rfl post
  apply sse_scalar_upper_branch program method vectorIndex smallIndex profile found false after frame args
    (armScalarUpper after right) post
  by_cases rightSmall : armScalarUpper after right = BitVec.ofNat 64 0
  · simp only [rightSmall, ite_true]
    have kept : inputLimb entered right 0 = inputLimb after right 0 := by
      rw [sse_input_limb_kept call setupPreserved (by simp), sse_input_limb_kept call afterPreserved (by simp)]
    rw [kept] at loaded
    exact sse_scalar_small_finish program method vectorIndex smallIndex profile found small false
      original after frame left right output home flag call afterCall afterPreserved afterNext owned slot loaded rightSmall
  · simp only [rightSmall, ite_false]
    apply sse_scalar_save_low program method vectorIndex smallIndex profile found true original.nextIdentity entered after
      [left, right] [output] frame args left afterCall (by simp) enteredWF homes authority rfl post
    intro leftHome later leftSlot leftLoaded laterPreserved laterCall laterAuthority
    have allPreserved := afterPreserved.trans laterPreserved
    have laterNext := arm_scalar_watermark original entered later frame homes enteredWF laterCall.1.1 laterAuthority
    apply sse_scalar_upper_loads program method vectorIndex smallIndex profile found true later frame args
      [left, right] [output] left laterCall (by simp) rfl post
    apply sse_scalar_upper_branch program method vectorIndex smallIndex profile found true later frame args
      (armScalarUpper later left) post
    by_cases leftSmall : armScalarUpper later left = BitVec.ofNat 64 0
    · simp only [leftSmall, ite_true]
      have kept : inputLimb after left 0 = inputLimb later left 0 := by
        rw [sse_input_limb_kept call afterPreserved (by simp), sse_input_limb_kept call allPreserved (by simp)]
      rw [kept] at leftLoaded
      exact sse_scalar_small_finish program method vectorIndex smallIndex profile found small true
        original later frame left right output leftHome flag call laterCall allPreserved laterNext owned leftSlot leftLoaded leftSmall
    · simp only [leftSmall, ite_false]
      exact sse_scalar_vector_finish program method vectorIndex smallIndex profile found helper sse42 original later frame left right output flag flagFit call laterCall allPreserved laterNext owned

/-- Certify the complete SSE dispatcher from its helper contracts. -/
theorem checked_sse_scalar_contract_of (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (helper : SSEHelperContract program vectorIndex) (small : PortableSmallContract program smallIndex)
    (disabled : profile.advSimd = false) (sse42 : profile.sse42 = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method
        (vector128Arguments left right output flag) memory fuel final returned ∧
      ARMScalarReportingPost memory final returned left right output flag := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, setup, homes, _, _⟩ := sse_scalar_frame_setup profile vectorIndex smallIndex memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    sse_scalar_entry program method vectorIndex smallIndex profile found helper small
      disabled sse42 memory entered left right output flag flagFit frame call setup homes
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method (sseScalarBody profile vectorIndex smallIndex)
      args memory frame entered fuel final returned found checked setup live executed, result⟩

/-- Certify the complete SSE dispatcher and all visited states from ordinary caller views. -/
theorem checked_sse_scalar_contract (program : CIL.Program) (method vectorIndex smallIndex carry storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (vectorFound : program[vectorIndex]? = some (sseBody profile carry storage))
    (smallFound : program[smallIndex]? = some (portableSmallBody profile storage))
    (carryFound : program[carry]? = some (UInt256Proof.Add.CarrySafety.carryBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (disabled : profile.advSimd = false) (sse2 : profile.sse2 = true) (ssse3 : profile.ssse3 = true) (sse42 : profile.sse42 = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method
        (vector128Arguments left right output flag) memory fuel final returned ∧
      ARMScalarReportingPost memory final returned left right output flag :=
  checked_sse_scalar_contract_of program method vectorIndex smallIndex profile found
    (sse_helper_contract profile disabled sse2 ssse3 program vectorIndex carry storage vectorFound carryFound storageFound)
    (portable_small_contract program smallIndex storage profile smallFound storageFound disabled)
    disabled sse42 memory left right output flag flagFit call

#print axioms sse_input_limb_kept
#print axioms sse_scalar_entry
#print axioms checked_sse_scalar_contract_of
#print axioms checked_sse_scalar_contract
end UInt256Proof.Add.Safety
