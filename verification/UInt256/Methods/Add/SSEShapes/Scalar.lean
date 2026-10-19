import UInt256.Methods.Add.SSEShapes.Helper

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- Small-operand tests and the SSE4.2 vector call, with branch targets relative to `base`. -/
def scalarCore (base vectorIndex smallIndex : Nat) : List CIL.Op := [
  .arg 1, .fieldAt 0 8, .setLocal 0, .arg 1, .fieldAt 8 8, .arg 1, .fieldAt 16 8, .bor, .arg 1, .fieldAt 24 8, .bor,
  .brnonzero (base + 17), .arg 0, .local 0, .arg 2, .call smallIndex 3, .ret (some .unsigned8),
  .arg 0, .fieldAt 0 8, .setLocal 1, .arg 0, .fieldAt 8 8, .arg 0, .fieldAt 16 8, .bor, .arg 0, .fieldAt 24 8, .bor,
  .brnonzero (base + 34), .arg 1, .local 1, .arg 2, .call smallIndex 3, .ret (some .unsigned8),
  .feature .sse42, .brzero (base + 42), .arg 0, .arg 1, .arg 2, .arg 3 (some .unsigned8), .call vectorIndex 4,
  .ret (some .unsigned8)]

/-- Start of the save block for the right (`false`) or left (`true`) operand. -/
def scalarSave (base : Nat) (swapped : Bool) : Nat := if swapped then base + 17 else base

/-- A scalar dispatcher: AdvSimd guard at entry, then the core at `base`, with word homes from `specs`. -/
structure ScalarShaped (body : CIL.Method) (base vectorIndex smallIndex : Nat) (doubled : Bool)
    (specs : List (Option (BitVec 64))) : Prop where
  guard : body.code = [] ++ guardCode doubled base ++ body.code.drop (guardCode doubled base).length
  core : At body.code base (scalarCore base vectorIndex smallIndex)
  returns : body.returnsValue = true
  metadata : body.localKinds = wordKinds specs ∧ body.locals = wordInitializers specs
  vectors : body.vectorArgs = []
  parameters : body.parameterHomes = []
  low : ∀ swapped : Bool, specs[if swapped then 1 else 0]? = some (some 0)

theorem scalar_frame_setup (body : CIL.Method) (specs : List (Option (BitVec 64)))
    (metadata : body.localKinds = wordKinds specs ∧ body.locals = wordInitializers specs)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame body args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity specs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨slots, owned, result, made, homes⟩ := make_word_locals memory memory.nextIdentity specs wellFormed
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have entered : enterFrame body args memory = .ok (frame, result) := by
    unfold enterFrame
    dsimp only
    rw [metadata.1, metadata.2, made, vectors, parameters]
    simp only [Bind.bind, Except.bind, makeArgumentHomes, makeParameterHomes, Pure.pure, Except.pure, List.map_nil, List.append_nil]
    rfl
  exact ⟨frame, result, entered, homes, enterFrame_preserves_caller_memory _ _ _ _ _ entered,
    enterFrame_preserves_wellFormed _ _ _ _ _ wellFormed entered⟩

/-- Original frame-home authority bounds the current allocation watermark. -/
theorem scalar_watermark (specs : List (Option (BitVec 64))) (low : specs[0]? = some (some 0))
    (original entered current : Memory) (frame : Frame)
    (homes : WordHomes entered original.nextIdentity specs frame.locals)
    (enteredWF : entered.WellFormed) (currentWF : current.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) :
    original.nextIdentity ≤ current.nextIdentity := by
  obtain ⟨home, _, fresh, _, writable⟩ := homes.word_at 0 0 low
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have retained := authority.access writable (enteredWF.1 _ _ ready.present).1
  obtain ⟨currentAllocation, currentReady⟩ := access_requirements retained
  exact Nat.le_trans fresh (Nat.le_of_lt (currentWF.1 _ _ currentReady.present).1)

/-- Save the selected operand's low limb in its private word home (right in local0, left in local1). -/
theorem scalar_save_low (program : CIL.Program) (body : CIL.Method) (method vectorIndex smallIndex : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ scalarCore base vectorIndex smallIndex ++ tail)
    (specs : List (Option (BitVec 64))) (low : ∀ swapped : Bool, specs[if swapped then 1 else 0]? = some (some 0))
    (swapped : Bool) (boundary : Nat) (entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (input : Reference)
    (call : CallingConditions program current inputs outputs) (member : input ∈ inputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary specs frame.locals)
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
        run program fuel method (scalarSave base swapped + 3) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (scalarSave base swapped) args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨home, slot, bound, _, writable⟩ := homes.word_at (if swapped then 1 else 0) (BitVec.ofNat 64 0) (low swapped)
  obtain ⟨after, loaded, preserved, afterCall, afterAuthority, _, stored⟩ :=
    checked_numeric_home_store program body
      boundary entered current inputs outputs frame call enteredWF authority (if swapped then 1 else 0)
      ⟨.word64, .i64 0, 0, rfl⟩ home slot bound writable (.i64 (inputLimb current input 0)) (inputLimb current input 0).toNat rfl
  have done := continuation home after slot loaded preserved afterCall afterAuthority
  have formed := call.input_formed member
  have field := call.input_field_instruction member 0
  dsimp at field
  cases swapped <;> simp only [scalarSave, Bool.false_eq_true, ite_false, ite_true, Nat.add_assoc, Nat.reduceAdd]
    at argument slot stored done ⊢
  all_goals
    repeat' (normalize_pc; first
      | exact done
      | (apply run_next_exists post found (by fetch_segment)
         first
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, formValue, formed, field, pureArity,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))))

/-- The three upper limbs of the selected operand are or-combined from checked field loads. -/
theorem scalar_upper_loads (program : CIL.Program) (body : CIL.Method) (method vectorIndex smallIndex : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ scalarCore base vectorIndex smallIndex ++ tail)
    (swapped : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (inputs outputs : List Reference) (input : Reference)
    (call : CallingConditions program memory inputs outputs) (member : input ∈ inputs)
    (argument : args[if swapped then 0 else 1]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (scalarSave base swapped + 11)
        args frame [.scalar (.i64 (armScalarUpper memory input))] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (scalarSave base swapped + 3)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
    have formed := call.input_formed member
    have loaded := call.input_field_instruction member
    have l1 := loaded 1
    have l2 := loaded 2
    have l3 := loaded 3
    dsimp at l1 l2 l3
    simp only [show (3 : Fin 4).val = 3 from rfl] at l3
    unfold armScalarUpper at continuation
    cases swapped <;> simp only [scalarSave, Bool.false_eq_true, ite_false, ite_true, Nat.add_assoc, Nat.reduceAdd]
      at argument continuation ⊢
    all_goals
      repeat' (normalize_pc; first
        | exact continuation
        | (apply run_next_exists post found (by fetch_segment)
           simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, numericValue, formValue, formed, l1, l2, l3, pureArity,
               scalars, CIL.step.eq_def, CIL.truth, CIL.binary,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- A zero upper part selects the small helper; otherwise control continues to the next test. -/
theorem scalar_upper_branch (program : CIL.Program) (body : CIL.Method) (method vectorIndex smallIndex : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ scalarCore base vectorIndex smallIndex ++ tail)
    (swapped : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (condition : BitVec 64) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method
        (if condition = BitVec.ofNat 64 0 then scalarSave base swapped + 12 else scalarSave base swapped + 17)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (scalarSave base swapped + 11)
        args frame [.scalar (.i64 condition)] memory = .ok (final, returned) ∧ post final returned := by
    cases swapped <;> by_cases zero : condition = BitVec.ofNat 64 0
    all_goals
      simp only [scalarSave, Bool.false_eq_true, ite_false, ite_true, zero, Nat.add_assoc, Nat.reduceAdd]
        at continuation ⊢
      apply run_next_exists post found (by fetch_segment) _ continuation
      simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth,
        show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, zero,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_frame_setup
#print axioms scalar_watermark
#print axioms scalar_save_low
#print axioms scalar_upper_loads
#print axioms scalar_upper_branch
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- The selected small route calls the small helper and forwards its byte flag. -/
theorem scalar_small_call (program : CIL.Program) (body : CIL.Method) (method vectorIndex smallIndex : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ scalarCore base vectorIndex smallIndex ++ tail)
    (returns : body.returnsValue = true) (smallContract : PortableSmallContract program smallIndex)
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
      run program fuel method (scalarSave base swapped + 12) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨childFuel, final, returned, certified, result⟩ :=
    smallContract memory source output word call
  have fi := call.input_formed (reference := source) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have stepped : ∀ pc, step body (.call smallIndex 3) pc args frame
      [.reference (.address output), .scalar (.i64 word), .reference (.address source)] memory =
        .ok (.call smallIndex (armSmallArguments source output word) [] memory) := by
    intro pc
    simp [step, armSmallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have wordLoad := fun (pc : Nat) (stack : List Value) => step_load_word64
    (body := body) (pc := pc) (args := args) (stack := stack) slot loaded
  have done := continuation childFuel final returned certified result
  have returnedRun : ∀ pc, body.code[pc]? = some (.ret (some .unsigned8)) →
      run program 1 method pc args frame (returned ++ []) final = .ok (leaveFrame frame final, returned) := by
    intro pc fetched
    rw [result.flag]
    split <;> simp [run, found, fetched, returns, step, checkedValue, numericValue, List.mapM, List.mapM.loop, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    all_goals rfl
  have callRun : ∀ pc, body.code[pc]? = some (.call smallIndex 3) → body.code[pc + 1]? = some (.ret (some .unsigned8)) →
      ∃ fuel final' returned', run program fuel method pc args frame
        [.reference (.address output), .scalar (.i64 word), .reference (.address source)] memory =
          .ok (final', returned') ∧ post final' returned' := fun pc callAt retAt =>
    let ⟨fuel, executed⟩ := run_call_exists found callAt (stepped pc) ⟨childFuel, certified.1⟩ ⟨1, returnedRun _ retAt⟩
    ⟨fuel, leaveFrame frame final, returned, executed, done⟩
  cases swapped <;> simp only [scalarSave, Bool.false_eq_true, ite_false, ite_true, Nat.add_assoc, Nat.reduceAdd]
    at slot sourceArg wordLoad ⊢
  · have finish := callRun (base + 15) (code_at code leadingLength rfl) (code_at (k := 16) code leadingLength rfl)
    repeat' (normalize_pc; first
      | exact finish
      | (apply run_next_exists post found (by fetch_segment)
         first
         | exact wordLoad _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, sourceArg, outputArg, checkedValue, formValue, fi, fo,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))))
  · have finish := callRun (base + 32) (code_at code leadingLength rfl) (code_at (k := 33) code leadingLength rfl)
    repeat' (normalize_pc; first
      | exact finish
      | (apply run_next_exists post found (by fetch_segment)
         first
         | exact wordLoad _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, sourceArg, outputArg, checkedValue, formValue, fi, fo,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))))

/-- The small route reaches the shared scalar reporting postcondition for either operand order. -/
theorem scalar_small_finish (program : CIL.Program) (body : CIL.Method) (method vectorIndex smallIndex : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ scalarCore base vectorIndex smallIndex ++ tail)
    (returns : body.returnsValue = true) (smallContract : PortableSmallContract program smallIndex)
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
      run program fuel method (scalarSave base swapped + 12) (vector128Arguments left right output flag) frame [] current =
        .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  have sums := arm_scalar_small_values program swapped original current left right output call preserved small
  apply scalar_small_call program body method vectorIndex smallIndex found leading tail base leadingLength code returns
    smallContract swapped current frame
    (vector128Arguments left right output flag) (if swapped then right else left) output home _ slot loaded
    (by cases swapped <;> rfl) rfl
    (arm_scalar_select_input program current [left, right] _ output currentCall (by cases swapped <;> simp))
  intro childFuel final returned certified result
  refine ⟨arm_scalar_retire original current final frame left right output returned call preserved next owned
    result.wellFormed (result.value.trans sums.1) ⟨_, result.flag⟩ result.writable result.footprint, ?_⟩
  intro _
  simpa only [sums.2] using result.flag

/-- With SSE4.2 enabled the dispatcher calls the vector helper and forwards its flag. -/
theorem scalar_vector_finish (program : CIL.Program) (body : CIL.Method) (method vectorIndex smallIndex : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ scalarCore base vectorIndex smallIndex ++ tail)
    (returns : body.returnsValue = true)
    (helper : SSEHelperContract program vectorIndex) (sse42 : body.profile.sse42 = true)
    (original current : Memory) (frame : Frame) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method (base + 34) (vector128Arguments left right output flag)
        frame [] current = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  obtain ⟨childFuel, final, returnedFlag, certified, result, returnedFit, overflow, writable, footprint⟩ :=
    helper current left right output flag flagFit currentCall
  have fl := currentCall.input_formed (reference := left) (by simp)
  have fr := currentCall.input_formed (reference := right) (by simp)
  have fo := currentCall.output_formed (reference := output) (by simp)
  have stepped : step body (.call vectorIndex 4) (base + 40)
      (vector128Arguments left right output flag) frame
      [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] current =
      .ok (.call vectorIndex (vector128Arguments left right output flag) [] current) := by
    simp [step, flagFit, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have fetched : body.code[base + 41]? = some (.ret (some .unsigned8)) := code_at code leadingLength rfl
  have returned : run program 1 method (base + 40 + 1)
      (vector128Arguments left right output flag) frame [.scalar (.i32 returnedFlag)] final =
      .ok (leaveFrame frame final, [.scalar (.i32 returnedFlag)]) := by
    simp [run, found, fetched, returns, step, returnedFit, List.mapM, List.mapM.loop, Option.bind, checkedValue, numericValue, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    try rfl
  obtain ⟨fuel, executed⟩ := run_call_exists found (code_at code leadingLength rfl) stepped ⟨_, certified.1⟩ ⟨1, returned⟩
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
      run program fuel method (base + 40) (vector128Arguments left right output flag)
        frame [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] current =
        .ok (final, returned) ∧ post final returned := ⟨fuel, _, _, executed, done⟩
  repeat' (normalize_pc; first
    | exact finish
    | (apply run_next_exists post found (by fetch_segment)
       simp (config := { implicitDefEqProofs := false })
         [step, flagFit, sse42, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo, pureArity, scalars,
           CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms scalar_small_call
#print axioms scalar_small_finish
#print axioms scalar_vector_finish
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- Complete dispatcher execution: both small-operand routes and the SSE4.2 vector route. -/
theorem scalar_entry (program : CIL.Program) (body : CIL.Method) (method base vectorIndex smallIndex : Nat) (doubled : Bool)
    (specs : List (Option (BitVec 64))) (found : program[method]? = some body)
    (shaped : ScalarShaped body base vectorIndex smallIndex doubled specs)
    (helper : SSEHelperContract program vectorIndex) (small : PortableSmallContract program smallIndex)
    (disabled : body.profile.advSimd = false) (sse42 : body.profile.sse42 = true)
    (original entered : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (frame : Frame)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame body (vector128Arguments left right output flag) original = .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity specs frame.locals) :
    ∃ fuel final returned,
      run program fuel method 0 (vector128Arguments left right output flag)
        frame [] entered = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let args := vector128Arguments left right output flag
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  obtain ⟨leading, tail, leadingLength, code⟩ := shaped.core
  have enteredCall := call.after_frame_setup setup
  have setupPreserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have enteredWF := enteredCall.1.1
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  have low0 : specs[0]? = some (some 0) := shaped.low false
  apply guard_skip program body method found [] _ 0 rfl doubled base shaped.guard disabled args [] frame entered post
  have startRight : scalarSave base false = base := rfl
  rw [← startRight]
  apply scalar_save_low program body method vectorIndex smallIndex found leading tail base leadingLength code specs shaped.low
    false original.nextIdentity entered entered [left, right] [output] frame args right enteredCall (by simp) enteredWF homes
    (MemoryBelow.refl _ _).accessBelow rfl post
  intro home after slot loaded preserved afterCall authority
  have afterPreserved := setupPreserved.trans preserved
  have afterNext := scalar_watermark specs low0 original entered after frame homes enteredWF afterCall.1.1 authority
  apply scalar_upper_loads program body method vectorIndex smallIndex found leading tail base leadingLength code false after frame args
    [left, right] [output] right afterCall (by simp) rfl post
  apply scalar_upper_branch program body method vectorIndex smallIndex found leading tail base leadingLength code false after frame args
    (armScalarUpper after right) post
  by_cases rightSmall : armScalarUpper after right = BitVec.ofNat 64 0
  · simp only [rightSmall, ite_true]
    have kept : inputLimb entered right 0 = inputLimb after right 0 := by
      rw [sse_input_limb_kept call setupPreserved (by simp), sse_input_limb_kept call afterPreserved (by simp)]
    rw [kept] at loaded
    exact scalar_small_finish program body method vectorIndex smallIndex found leading tail base leadingLength code shaped.returns
      small false original after frame left right output home flag call afterCall afterPreserved afterNext owned slot loaded rightSmall
  · simp only [rightSmall, ite_false]
    have startLeft : scalarSave base false + 17 = scalarSave base true := rfl
    rw [startLeft]
    apply scalar_save_low program body method vectorIndex smallIndex found leading tail base leadingLength code specs shaped.low
      true original.nextIdentity entered after [left, right] [output] frame args left afterCall (by simp) enteredWF homes authority
      rfl post
    intro leftHome later leftSlot leftLoaded laterPreserved laterCall laterAuthority
    have allPreserved := afterPreserved.trans laterPreserved
    have laterNext := scalar_watermark specs low0 original entered later frame homes enteredWF laterCall.1.1 laterAuthority
    apply scalar_upper_loads program body method vectorIndex smallIndex found leading tail base leadingLength code true later frame args
      [left, right] [output] left laterCall (by simp) rfl post
    apply scalar_upper_branch program body method vectorIndex smallIndex found leading tail base leadingLength code true later frame args
      (armScalarUpper later left) post
    by_cases leftSmall : armScalarUpper later left = BitVec.ofNat 64 0
    · simp only [leftSmall, ite_true]
      have kept : inputLimb after left 0 = inputLimb later left 0 := by
        rw [sse_input_limb_kept call afterPreserved (by simp), sse_input_limb_kept call allPreserved (by simp)]
      rw [kept] at leftLoaded
      exact scalar_small_finish program body method vectorIndex smallIndex found leading tail base leadingLength code shaped.returns
        small true original later frame left right output leftHome flag call laterCall allPreserved laterNext owned leftSlot leftLoaded leftSmall
    · simp only [leftSmall, ite_false]
      have startVector : scalarSave base true + 17 = base + 34 := by simp [scalarSave, Nat.add_assoc]
      rw [startVector]
      exact scalar_vector_finish program body method vectorIndex smallIndex found leading tail base leadingLength code shaped.returns
        helper sse42 original later frame left right output flag flagFit call laterCall allPreserved laterNext owned

/-- Certify a shaped dispatcher from its helper contracts. -/
theorem checked_scalar_contract (program : CIL.Program) (body : CIL.Method) (method base vectorIndex smallIndex : Nat) (doubled : Bool)
    (specs : List (Option (BitVec 64))) (found : program[method]? = some body)
    (shaped : ScalarShaped body base vectorIndex smallIndex doubled specs)
    (helper : SSEHelperContract program vectorIndex) (small : PortableSmallContract program smallIndex)
    (disabled : body.profile.advSimd = false) (sse42 : body.profile.sse42 = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method
        (vector128Arguments left right output flag) memory fuel final returned ∧
      ARMScalarReportingPost memory final returned left right output flag := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    scalar_frame_setup body specs shaped.metadata shaped.vectors shaped.parameters memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    scalar_entry program body method base vectorIndex smallIndex doubled specs found shaped helper small
      disabled sse42 memory entered left right output flag flagFit frame call setup homes
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method body args memory frame entered fuel final returned found checked setup live executed, result⟩

#print axioms scalar_entry
#print axioms checked_scalar_contract
end UInt256Proof.Add.SSEShapes
