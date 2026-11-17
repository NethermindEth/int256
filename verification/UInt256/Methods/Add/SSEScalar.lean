import UInt256.Generated.MethodTemplates
import UInt256.Methods.Add.SSEEntry
import UInt256.Methods.Add.PortableSmall
import UInt256.Methods.Add.ARMScalarEntry

namespace UInt256Proof.Add.Safety

open CIL.Safety UInt256Model.Safety

-- AddScalar with AdvSimd disabled: right-small, left-small, then the SSE4.2 vector helper.
def sseScalarBody (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method1
      $(Lean.mkIdent `profile) false true $(Lean.mkIdent `smallIndex)
      $(Lean.mkIdent `vectorIndex) 0 0)) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

theorem sse_scalar_frame_setup (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame (sseScalarBody profile vectorIndex smallIndex) args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity armScalarLocalSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  word_frame_setup _ armScalarLocalSpecs (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    memory args wellFormed

/-- Where each small-operand test starts: the right operand first, then the left. -/
def sseSaveStart (swapped : Bool) : Nat := if swapped then 58 else 41

/-- Save the selected operand's low limb in its private word home (right in local0, left in
    local1), then test its upper limbs: zero selects the small helper, otherwise the next test. -/
theorem sse_scalar_test (program : CIL.Program) (method vectorIndex smallIndex : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
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
      ∃ fuel final returned, run program fuel method (sseSaveStart swapped +
          if armScalarUpper after input = BitVec.ofNat 64 0 then 12 else 17) args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel method (sseSaveStart swapped) args frame [] current =
      .ok (final, returned) ∧ post final returned := by
  obtain ⟨home, slot, bound, _, writable⟩ := homes.word_at (if swapped then 1 else 0)
    (BitVec.ofNat 64 0) (by cases swapped <;> rfl)
  obtain ⟨after, loaded, preserved, afterCall, afterAuthority, _, stored⟩ :=
    checked_numeric_home_store program (sseScalarBody profile vectorIndex smallIndex)
      boundary entered current inputs outputs frame call enteredWF authority
      (if swapped then 1 else 0) ⟨.word64, .i64 0, 0, rfl⟩ home slot bound writable
      (.i64 (inputLimb current input 0)) (inputLimb current input 0).toNat rfl
  have done := continuation home after slot loaded preserved afterCall afterAuthority
  have upper := afterCall.input_field_instruction member
  unfold armScalarUpper at done
  cases swapped <;> by_cases small : inputLimb after input 1 ||| inputLimb after input 2 |||
    inputLimb after input 3 = BitVec.ofNat 64 0
  all_goals
    simp only [sseSaveStart, small, Bool.false_eq_true, ite_true, ite_false, Nat.reduceAdd]
      at argument stored done ⊢
    cil_contract_steps [found, argument, call.input_formed member, afterCall.input_formed member,
      call.input_field_instruction member 0, upper 1, upper 2, upper 3, stored, small] until done
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


/-- The small route calls the certified portable helper, forwards its byte flag and reaches
    the shared scalar reporting postcondition for either operand order. -/
theorem sse_scalar_small_finish (program : CIL.Program) (method vectorIndex smallIndex : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (smallContract : PortableSmallContract program smallIndex)
    (swapped : Bool) (original current : Memory) (frame : Frame)
    (left right output home : Reference) (flag : BitVec 32)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (slot : frame.locals[if swapped then 1 else 0]? = some (.bytes .word64 home))
    (loaded : read current home 8 1 =
      .ok (numberBytes (inputLimb current (if swapped then left else right) 0).toNat 8))
    (small : armScalarUpper current (if swapped then left else right) = BitVec.ofNat 64 0) :
    ∃ fuel final returned,
      run program fuel method (sseSaveStart swapped + 12)
        (vector128Arguments left right output flag) frame [] current = .ok (final, returned) ∧
      ARMScalarReportingPost original final returned left right output flag := by
  have sums := arm_scalar_small_values program swapped original current left right output call
    preserved small
  have selected := arm_scalar_select_input program current [left, right]
    (if swapped then right else left) output currentCall (by cases swapped <;> simp)
  obtain ⟨childFuel, final, returned, certified, result⟩ := smallContract current _ output
    (inputLimb current (if swapped then left else right) 0) selected
  obtain ⟨carry, shaped⟩ : ∃ carry, returned = [.scalar (.i32 carry)] := ⟨_, result.flag⟩
  subst shaped
  have carryFit : CIL.NarrowKind.unsigned8.extend carry = carry := by
    rw [CIL.Value.i32.inj (Value.scalar.inj (List.cons.inj result.flag).1)]
    exact CIL.NarrowKind.extend_ite_one_zero _ _
  have sourceFormed := selected.input_formed (reference := if swapped then right else left)
    (by simp)
  have outputFormed := selected.output_formed (reference := output) (by simp)
  have wordLoad := fun (pc : Nat) (stack : List Value) => step_load_word64
    (body := sseScalarBody profile vectorIndex smallIndex) (pc := pc)
    (args := vector128Arguments left right output flag) (stack := stack) slot loaded
  have reported := result.flag
  simp only [sums.2] at reported
  apply WP.exists_execution
  cases swapped <;> simp only [sseSaveStart, Bool.false_eq_true, ite_false, ite_true]
    at slot sourceFormed wordLoad certified ⊢
  all_goals
    cil_contract_steps 3 [found, vector128Arguments, wordLoad, sourceFormed, outputFormed]
    apply WP.adequate.mp
    apply WP.call (helperPost := fun reached =>
        reached.1 = final ∧ reached.2 = [.scalar (.i32 carry)]) found (by rfl)
      (by cil_checked_step [armSmallArguments, sourceFormed, outputFormed])
      ⟨childFuel, _, certified.1, rfl, rfl⟩
    rintro _ _ ⟨rfl, rfl⟩
    cil_contract_steps [found, carryFit]
    exact ⟨arm_scalar_retire original current _ frame left right output _ call preserved next
      owned result.wellFormed (result.value.trans sums.1) ⟨_, rfl⟩ result.writable
      result.footprint, fun _ => reported⟩

/-- With SSE4.2 enabled the dispatcher calls the certified vector helper and forwards its flag. -/
theorem sse_scalar_vector_finish (program : CIL.Program) (method vectorIndex smallIndex : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (sseScalarBody profile vectorIndex smallIndex))
    (helper : SSEHelperContract program vectorIndex) (sse42 : profile.sse42 = true)
    (original current : Memory) (frame : Frame) (left right output : Reference) (flag : BitVec 32)
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 75 (vector128Arguments left right output flag)
        frame [] current = .ok (final, returned) ∧
      ARMScalarReportingPost original final returned left right output flag := by
  obtain ⟨childFuel, final, returnedFlag, certified, result, returnedFit, overflow, writable,
    footprint⟩ := helper current left right output flag flagFit currentCall
  have leftFormed := currentCall.input_formed (reference := left) (by simp)
  have rightFormed := currentCall.input_formed (reference := right) (by simp)
  have outputFormed := currentCall.output_formed (reference := output) (by simp)
  have kept : ∀ reference ∈ [left, right],
      inputValue current reference = inputValue original reference := fun reference member => by
    simp only [inputValue, call.input_bytes_of_memory_below preserved member]
  rw [kept left (by simp), kept right (by simp)] at result overflow
  have called : WP (Execution (fun fuel => run program fuel method 81
      (vector128Arguments left right output flag) frame
      [.scalar (.i32 flag), .reference (.address output), .reference (.address right),
        .reference (.address left)] current))
      (fun reached => ARMScalarReportingPost original reached.1 reached.2 left right output
        flag) := by
    apply WP.call (helperPost := fun reached =>
        reached.1 = final ∧ reached.2 = [.scalar (.i32 returnedFlag)]) found (by rfl)
      (by cil_checked_step [vector128Arguments, flagFit, leftFormed, rightFormed, outputFormed])
      ⟨childFuel, _, certified.1, rfl, rfl⟩
    rintro _ _ ⟨rfl, rfl⟩
    cil_contract_steps [found, returnedFit]
    exact ⟨arm_scalar_retire original current _ frame left right output _ call preserved next
      owned (invoke_preserves_wellFormed _ _ _ _ _ _ _ currentCall.1.1 certified.1) result
      ⟨returnedFlag, rfl⟩ writable (fun id old offset untouched => footprint id offset old
        untouched), fun reporting => by rw [overflow reporting]⟩
  have bodyProfile : (sseScalarBody profile vectorIndex smallIndex).profile = profile := rfl
  cil_contract_steps [found, sse42, bodyProfile, CIL.FeatureProfile.evaluate, vector128Arguments,
    flagFit, leftFormed, rightFormed, outputFormed] until called

/-- Caller memory kept below the watermark keeps every limb of both operands. -/
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
  have bodyProfile : (sseScalarBody profile vectorIndex smallIndex).profile = profile := rfl
  suffices tested : ∃ fuel final returned, run program fuel method (sseSaveStart false) args
      frame [] entered = .ok (final, returned) ∧ post final returned by
    cil_contract_steps [found, disabled, bodyProfile, CIL.FeatureProfile.evaluate] until tested
  apply sse_scalar_test program method vectorIndex smallIndex profile found false
    original.nextIdentity entered entered [left, right] [output] frame args right enteredCall
    (by simp) enteredWF homes (MemoryBelow.refl _ _).accessBelow rfl post
  intro home after slot loaded preserved afterCall authority
  have afterPreserved := setupPreserved.trans preserved
  have afterNext := arm_scalar_watermark original entered after frame homes enteredWF afterCall.1.1 authority
  by_cases rightSmall : armScalarUpper after right = BitVec.ofNat 64 0
  · simp only [rightSmall, ite_true]
    have kept : inputLimb entered right 0 = inputLimb after right 0 := by
      rw [sse_input_limb_kept call setupPreserved (by simp), sse_input_limb_kept call afterPreserved (by simp)]
    rw [kept] at loaded
    exact sse_scalar_small_finish program method vectorIndex smallIndex profile found small false
      original after frame left right output home flag call afterCall afterPreserved afterNext owned slot loaded rightSmall
  · simp only [rightSmall, ite_false]
    apply sse_scalar_test program method vectorIndex smallIndex profile found true
      original.nextIdentity entered after [left, right] [output] frame args left afterCall
      (by simp) enteredWF homes authority rfl post
    intro leftHome later leftSlot leftLoaded laterPreserved laterCall laterAuthority
    have allPreserved := afterPreserved.trans laterPreserved
    have laterNext := arm_scalar_watermark original entered later frame homes enteredWF laterCall.1.1 laterAuthority
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
    (sse_helper_checked profile disabled sse2 ssse3 program vectorIndex carry storage
      vectorFound carryFound storageFound)
    (checked_portable_small_contract program smallIndex storage profile smallFound
      storageFound disabled)
    disabled sse42 memory left right output flag flagFit call

end UInt256Proof.Add.Safety