import UInt256.Methods.Add.Vector256Prepare
import UInt256.Safety.ReportingContract

namespace UInt256Proof.Add.Vector256
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety
variable {identity : Nat} {assembly : String}

def entrySpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩,
   ⟨.vector256, .v256 0, 0, rfl⟩]

/-- The entry's four vector locals after `PrepareAdd` returns. -/
def entryLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  fun index => (preparedCells left right index).map .v256

theorem four_cells {h0 h1 h2 h3 : Reference} {P : Nat → Reference → Prop}
    (p0 : P 0 h0) (p1 : P 1 h1) (p2 : P 2 h2) (p3 : P 3 h3) :
    ∀ (index : Nat) (cell : Reference), [h0, h1, h2, h3][index]? = some cell → P index cell := by
  intro index cell found
  rcases index with _ | _ | _ | _ | index <;> simp at found <;> subst found <;> assumption

set_option hygiene false in
/-- One pure entry instruction; expects `post found features profileEq state left right output`. -/
macro "entry_pure" : tactic => `(tactic|
  (have formedLeft := state.call.input_formed (reference := left) (by simp)
   have formedRight := state.call.input_formed (reference := right) (by simp)
   have formedOutput := state.call.output_formed (reference := output) (by simp)
   apply run_next_exists post found (by first | assumption | rfl)
   · simp (config := { implicitDefEqProofs := false })
       [step, cil_guard, observerCount, pureArity.eq_def, binaryArguments, checkedValue, numericValue, formValue, formedLeft, formedRight,
         formedOutput, staticInstruction, memoryInstruction, checkedAt, profileEq, features.avx, features.avx2,
         CIL.FeatureProfile.evaluate, scalars, checkedIntrinsic, CIL.Intrinsic.available, CIL.step.eq_def,
         CIL.binary.eq_def, CIL.unary.eq_def, CIL.truth, instruction.eq_def, Except.mapError, Bind.bind, Except.bind, Pure.pure,
         Except.pure]
     try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

set_option hygiene false in
macro "entry_address" : tactic => `(tactic|
  (apply run_next_exists post found (by first | assumption | rfl)
   · simp [step, cil_guard, observerCount, slot0, slot1, slot2, slot3, localAddress, formValue, formed0, formed1, formed2, formed3,
       checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
     try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- Both entries up to `PrepareAdd`: the speculative sum is stored and the four lane vectors are locals. -/
theorem entry_prepare (program : CIL.Program) (method prepare : Nat) (body : CIL.Method)
    (profile : CIL.FeatureProfile) (avx512 : Bool) (target : Nat)
    (found : program[method]? = some body) (profileEq : body.profile = profile)
    (f0 : body.code[0]? = some (.feature .avx2)) (f1 : body.code[1]? = some (.brzero target))
    (f2 : body.code[2]? = some (.arg 0)) (f3 : body.code[3]? = some (.arg 1))
    (f4 : body.code[4]? = some (.arg 2)) (f5 : body.code[5]? = some (.localAddr 0))
    (f6 : body.code[6]? = some (.localAddr 1)) (f7 : body.code[7]? = some (.localAddr 2))
    (f8 : body.code[8]? = some (.localAddr 3)) (f9 : body.code[9]? = some (.call prepare 7))
    (prepareContract : PrepareContract program prepare)
    (features : AddProfile profile avx512)
    (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (setup : enterFrame body (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WritableHomes entered memory.nextIdentity (entrySpecs.map NumericLocalSpec.kind) frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program memory entered after [left, right] output frame
        (entryLocals (inputValue memory left) (inputValue memory right))
        (some (fastSum (inputValue memory left) (inputValue memory right))) →
      ∃ fuel final values,
        run program fuel method 10 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (final, values) ∧ post final values := by
  have state := VectorFrame.initial call setup
  obtain ⟨h0, slot0, bound0, ready0⟩ := homes.home_at 0 .vector256 rfl
  obtain ⟨h1, slot1, bound1, ready1⟩ := homes.home_at 1 .vector256 rfl
  obtain ⟨h2, slot2, bound2, ready2⟩ := homes.home_at 2 .vector256 rfl
  obtain ⟨h3, slot3, bound3, ready3⟩ := homes.home_at 3 .vector256 rfl
  have formed0 := access_reference_valid _ _ _ _ _ ready0
  have formed1 := access_reference_valid _ _ _ _ _ ready1
  have formed2 := access_reference_valid _ _ _ _ _ ready2
  have formed3 := access_reference_valid _ _ _ _ _ ready3
  have live (h : Reference) (ready : access entered h (localWidth .vector256) 1 true = .ok ()) :
      h.allocation < entered.nextIdentity := by
    obtain ⟨allocation, requirements⟩ := access_requirements ready
    exact (state.enteredWF.1 _ _ requirements.present).1
  have slots : ∀ (index : Nat) (cell : Reference), [h0, h1, h2, h3][index]? = some cell →
      frame.locals[index]? = some (LocalSlot.bytes .vector256 cell) :=
    four_cells (P := fun index cell => frame.locals[index]? = some (LocalSlot.bytes .vector256 cell))
      slot0 slot1 slot2 slot3
  have layout : ScratchLayout memory.nextIdentity entered.nextIdentity [h0, h1, h2, h3] :=
    ⟨four_cells (P := fun _ cell => memory.nextIdentity ≤ cell.allocation ∧ cell.allocation < entered.nextIdentity)
      ⟨bound0, live h0 ready0⟩ ⟨bound1, live h1 ready1⟩ ⟨bound2, live h2 ready2⟩ ⟨bound3, live h3 ready3⟩,
     fun i j first second different hi hj =>
      homes.distinct i j .vector256 .vector256 first second different (slots i first hi) (slots j second hj)⟩
  have scratch : ScratchCells entered [h0, h1, h2, h3] (fun _ => none) :=
    four_cells (P := fun index cell => access entered cell 32 1 true = .ok () ∧
        ∀ value, (fun _ => none : Nat → Option (BitVec 256)) index = some value →
          CIL.Safety.read entered cell 32 1 = .ok (numberBytes value.toNat 32))
      ⟨ready0, fun _ none => by cases none⟩ ⟨ready1, fun _ none => by cases none⟩
      ⟨ready2, fun _ none => by cases none⟩ ⟨ready3, fun _ none => by cases none⟩
  obtain ⟨childFuel, after, invoked, conditions, grown, authority, footprint, result, cells⟩ :=
    prepareContract memory entered left right output
      h0 h1 h2 h3 call state.call state.enteredBound (fun id old offset => state.caller id old offset (Or.inl rfl))
      layout scratch
  have defined : ∀ (index : Nat) (value : BitVec 256),
      preparedCells (inputValue memory left) (inputValue memory right) index = some value →
      ∃ cell : Reference, [h0, h1, h2, h3][index]? = some cell := by
    intro index value specified
    rcases index with _ | _ | _ | _ | index
    · exact ⟨h0, rfl⟩
    · exact ⟨h1, rfl⟩
    · exact ⟨h2, rfl⟩
    · exact ⟨h3, rfl⟩
    · simp [preparedCells, maskCells, inputCells, rememberCell] at specified
  have next := VectorFrame.after_child state conditions grown authority footprint result
    (ScratchCells.known_locals cells slots defined)
  obtain ⟨fuel, final, values, ran, satisfied⟩ := continuation after next
  entry_pure
  entry_pure
  entry_pure
  entry_pure
  entry_pure
  entry_address
  entry_address
  entry_address
  entry_address
  have formedLeft := state.call.input_formed (reference := left) (by simp)
  have formedRight := state.call.input_formed (reference := right) (by simp)
  have formedOutput := state.call.output_formed (reference := output) (by simp)
  have stepped : step body (.call prepare 7) 9 (binaryArguments left right output) frame
      [.reference (.address h3), .reference (.address h2), .reference (.address h1), .reference (.address h0),
       .reference (.address output), .reference (.address right), .reference (.address left)] entered =
      .ok (.call prepare (prepareArguments left right output h0 h1 h2 h3) [] entered) := by
    simp [step, cil_guard, observerCount, prepareArguments, checkedValue, formValue, formedLeft, formedRight, formedOutput,
      formed0, formed1, formed2, formed3, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
      Except.pure]
  obtain ⟨total, composed⟩ := run_call_exists found f9 stepped ⟨childFuel, invoked⟩ ⟨fuel, by simpa using ran⟩
  exact ⟨total, final, values, composed, satisfied⟩

#print axioms entry_prepare

set_option hygiene false in
macro "entry_load" : tactic => `(tactic|
  apply VectorFrame.run_load post state found (by rfl) (by rfl))

theorem entry_setup (program : CIL.Program) (body : CIL.Method) (memory : Memory)
    (left right output : Reference) (call : CallingConditions program memory [left, right] [output])
    (kinds : body.localKinds = entrySpecs.map NumericLocalSpec.kind)
    (initializers : body.locals = entrySpecs.map NumericLocalSpec.value)
    (arguments : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (opaqueLocals : body.opaqueVectorLocals = []) :
    ∃ frame entered,
      enterFrame body (binaryArguments left right output) memory = .ok (frame, entered) ∧
      LiveState program (binaryArguments left right output) frame [] entered ∧
      WritableHomes entered memory.nextIdentity (entrySpecs.map NumericLocalSpec.kind) frame.locals ∧
      ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := by
  obtain ⟨frame, entered, setup, numeric, _, _⟩ := numeric_frame_setup body entrySpecs kinds initializers
    arguments parameters opaqueLocals memory (binaryArguments left right output) call.1.1
  exact ⟨frame, entered, setup, call.binary_entry_live setup, UInt256Model.Safety.NumericHomes.writable numeric,
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1⟩

set_option hygiene false in
/-- A branch step that also rewrites with the decided guard `selected`. -/
macro "entry_branch" : tactic => `(tactic|
  (apply run_next_exists post found (by rfl)
   · first | (simp only [selected]; rfl) | rfl))

/-- Caller guarantees of the Add entry: wrapped sum, writable output, other caller bytes kept. -/
def AddPost (memory : Memory) (left right output : Reference) (final : Memory) : Prop :=
  inputValue final output = inputValue memory left + inputValue memory right ∧
    access final output 32 1 true = .ok () ∧
    ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = memory.cells id offset

/-- The `Add` entry after `PrepareAdd`: the fast return or the `FinishAdd` correction. -/
theorem add_tail (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool) (finish prepare : Nat)
    (found : program[0]? = some (addEntryBody profile finish prepare))
    (finishContract : FinishContract program finish)
    (features : AddProfile profile avx512)
    (memory entered after : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id)
    (state : VectorFrame program memory entered after [left, right] output frame
      (entryLocals (inputValue memory left) (inputValue memory right))
      (some (fastSum (inputValue memory left) (inputValue memory right)))) :
    ∃ fuel final values,
      run program fuel 0 10 (binaryArguments left right output) frame [] after = .ok (final, values) ∧
        values = [] ∧ AddPost memory left right output final := by
  have profileEq : (addEntryBody profile finish prepare).profile = profile := rfl
  let post : Memory → List Value → Prop := fun final values => values = [] ∧ AddPost memory left right output final
  have returns : (addEntryBody profile finish prepare).returnsValue = false := rfl
  have retFetch : (addEntryBody profile finish prepare).code[24]? = some .ret := rfl
  generalize ha : inputValue memory left = a at state
  generalize hb : inputValue memory right = b at state
  entry_load
  entry_load
  entry_pure
  entry_pure
  entry_pure
  entry_pure
  entry_pure
  by_cases guard : parentPropagationBits (propagationMask (CIL.Vector.zip256 (· + ·) a b))
      (incomingCarry (generatedCarry a b)) = BitVec.ofNat 32 0
  · have selected : CIL.Vector.moveMask64 (propagationMask (CIL.Vector.zip256 (· + ·) a b) &&&
        incomingCarry (generatedCarry a b)) &&& 6#32 = 0#32 := guard
    entry_branch
    obtain ⟨value, access, footprint⟩ := state.finish call owned
    refine ⟨1, _, _, ?_, rfl, by rw [ha, hb]; exact value.trans (fast_sum_value a b guard), access, footprint⟩
    exact run_return found retFetch rfl rfl
  · have selected : (CIL.Vector.moveMask64 (propagationMask (CIL.Vector.zip256 (· + ·) a b) &&&
        incomingCarry (generatedCarry a b)) &&& 6#32 != 0) = true := bne_iff_ne.mpr guard
    entry_branch
    simp only [selected, ↓reduceIte]
    entry_load
    entry_load
    entry_load
    entry_pure
    let sum := CIL.Vector.zip256 (· + ·) a b
    have formedOutput := state.call.output_formed (reference := output) (by simp)
    have stepped : step (addEntryBody profile finish prepare) (.call finish 4) 22 (binaryArguments left right output) frame
        [.reference (.address output), .scalar (.v256 (propagationMask sum)),
         .scalar (.v256 (generatedCarry a b)), .scalar (.v256 sum)] after =
        .ok (.call finish (finishArguments sum (generatedCarry a b) (propagationMask sum) output) [] after) := by
      simp [step, cil_guard, observerCount, finishArguments, checkedValue, numericValue, formValue, formedOutput, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨childFuel, finished, invoked, result, writable, footprint⟩ :=
      finishContract after output state.call.without_inputs sum (generatedCarry a b) (propagationMask sum)
    obtain ⟨value, access, kept⟩ := state.finish_child call owned result writable footprint
    have popFetch : (addEntryBody profile finish prepare).code[23]? = some .pop := rfl
    have tail : run program 2 0 23 (binaryArguments left right output) frame
        ([.scalar (.i32 (finishFlag (generatedCarry a b) (propagationMask sum)))] ++ []) finished =
        .ok (leaveFrame frame finished, []) :=
      (run_next found popFetch rfl).trans (run_return found retFetch rfl rfl)
    obtain ⟨total, ran⟩ := run_call_exists found rfl stepped ⟨childFuel, invoked⟩ ⟨2, tail⟩
    exact ⟨total, _, _, ran, rfl, by rw [ha, hb]; exact value.trans (cascade_sum_value a b), access, kept⟩

#print axioms add_tail

/-- Caller guarantees of the AddOverflow entry: exact initial-operand carry and the Add guarantees. -/
def overflowFlag (memory : Memory) (left right : Reference) : BitVec 32 :=
  if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0

theorem overflow_tail (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool) (finish prepare : Nat)
    (found : program[0]? = some (addOverflowEntryBody profile finish prepare))
    (finishContract : FinishContract program finish)
    (features : AddProfile profile avx512)
    (memory entered after : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id)
    (state : VectorFrame program memory entered after [left, right] output frame
      (entryLocals (inputValue memory left) (inputValue memory right))
      (some (fastSum (inputValue memory left) (inputValue memory right)))) :
    ∃ fuel final values,
      run program fuel 0 10 (binaryArguments left right output) frame [] after = .ok (final, values) ∧
        values = [.scalar (.i32 (overflowFlag memory left right))] ∧ AddPost memory left right output final := by
  have profileEq : (addOverflowEntryBody profile finish prepare).profile = profile := rfl
  let post : Memory → List Value → Prop := fun final values =>
    values = [.scalar (.i32 (overflowFlag memory left right))] ∧ AddPost memory left right output final
  have returns : (addOverflowEntryBody profile finish prepare).returnsValue = true := rfl
  generalize ha : inputValue memory left = a at state
  generalize hb : inputValue memory right = b at state
  have retEq : ∀ (pc : Nat) (flag : BitVec 32),
      (addOverflowEntryBody profile finish prepare).code[pc]? = some (.ret (some .unsigned8)) →
      CIL.NarrowKind.unsigned8.extend flag = flag → ∀ m : Memory,
      run program 1 0 pc (binaryArguments left right output) frame [.scalar (.i32 flag)] m =
        .ok (leaveFrame frame m, [.scalar (.i32 flag)]) := by
    intro pc flag fetched normalized m
    simp [run, found, fetched, returns, step, cil_guard, observerCount, normalized, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  entry_load
  entry_load
  entry_pure
  by_cases guard : propagationMask (CIL.Vector.zip256 (· + ·) a b) &&& incomingCarry (generatedCarry a b) =
      BitVec.ofNat 256 0
  · simp only [guard, ↓reduceIte]
    entry_pure
    entry_load
    entry_pure
    entry_pure
    entry_pure
    entry_pure
    entry_pure
    entry_pure
    obtain ⟨value, access, footprint⟩ := state.finish call owned
    refine ⟨1, _, _, retEq 27 _ rfl (by split <;> rfl) after, ?_,
      by rw [ha, hb]; exact value.trans (fast_sum_value a b (parent_of_full _ _ guard)), access, footprint⟩
    unfold overflowFlag
    rw [ha, hb, ← fast_flag_value a b guard]
    rfl
  · simp only [guard, ↓reduceIte]
    entry_pure
    entry_load
    entry_load
    entry_load
    entry_pure
    let sum := CIL.Vector.zip256 (· + ·) a b
    have formedOutput := state.call.output_formed (reference := output) (by simp)
    have stepped : step (addOverflowEntryBody profile finish prepare) (.call finish 4) 18 (binaryArguments left right output) frame
        [.reference (.address output), .scalar (.v256 (propagationMask sum)),
         .scalar (.v256 (generatedCarry a b)), .scalar (.v256 sum)] after =
        .ok (.call finish (finishArguments sum (generatedCarry a b) (propagationMask sum) output) [] after) := by
      simp [step, cil_guard, observerCount, finishArguments, checkedValue, numericValue, formValue, formedOutput, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨childFuel, finished, invoked, result, writable, footprint⟩ :=
      finishContract after output state.call.without_inputs sum (generatedCarry a b) (propagationMask sum)
    obtain ⟨value, access, kept⟩ := state.finish_child call owned result writable footprint
    have normalized : CIL.NarrowKind.unsigned8.extend (finishFlag (generatedCarry a b) (propagationMask sum)) =
        finishFlag (generatedCarry a b) (propagationMask sum) := by
      unfold finishFlag
      split <;> rfl
    obtain ⟨total, ran⟩ := run_call_exists found rfl stepped ⟨childFuel, invoked⟩
      ⟨1, by simpa using retEq 19 _ rfl normalized finished⟩
    refine ⟨total, _, _, ran, ?_, by rw [ha, hb]; exact value.trans (cascade_sum_value a b), access, kept⟩
    unfold overflowFlag
    rw [ha, hb, ← cascade_flag_value a b]
    rfl

#print axioms overflow_tail

theorem binary_checked {program : CIL.Program} {memory : Memory} {left right output : Reference}
    (call : CallingConditions program memory [left, right] [output]) :
    (binaryArguments left right output).mapM (checkedValue memory) = .ok (binaryArguments left right output) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Public AVX2 `Add` from the callee contracts: wrapped sum, checked return, writable output, caller bytes kept. -/
theorem add_contract_of_callees (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (finish prepare : Nat)
    (entryFound : program[0]? = some (addEntryBody profile finish prepare))
    (finishContract : FinishContract program finish) (prepareContract : PrepareContract program prepare)
    (features : AddProfile profile avx512) :
    WrappingBinaryContract (· + ·) program 0 := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live, homes, owned⟩ := entry_setup program (addEntryBody profile finish prepare)
    memory left right output call rfl rfl rfl rfl rfl
  have finished : ∃ fuel final values,
      run program fuel 0 0 (binaryArguments left right output) frame [] entered = .ok (final, values) ∧
        values = [] ∧ AddPost memory left right output final := by
    apply entry_prepare program 0 prepare (addEntryBody profile finish prepare) profile avx512 25 entryFound rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl prepareContract features memory entered left right output frame
      call setup homes
    intro after state
    exact add_tail program profile avx512 finish prepare entryFound finishContract features memory entered after
      left right output frame call owned state
  obtain ⟨fuel, final, values, ran, empty, value, access, footprint⟩ := finished
  subst empty
  exact ⟨fuel, final, certify_invocation program 0 _ _ memory frame entered fuel final [] entryFound
    (binary_checked call) setup live ran, value, access, footprint⟩

/-- Public AVX2 `AddOverflow` from the callee contracts: exact carry, wrapped sum, caller bytes kept. -/
theorem add_overflow_contract_of_callees (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (finish prepare : Nat)
    (entryFound : program[0]? = some (addOverflowEntryBody profile finish prepare))
    (finishContract : FinishContract program finish) (prepareContract : PrepareContract program prepare)
    (features : AddProfile profile avx512) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program 0 := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live, homes, owned⟩ := entry_setup program
    (addOverflowEntryBody profile finish prepare) memory left right output call rfl rfl rfl rfl rfl
  have finished : ∃ fuel final values,
      run program fuel 0 0 (binaryArguments left right output) frame [] entered = .ok (final, values) ∧
        values = [.scalar (.i32 (overflowFlag memory left right))] ∧ AddPost memory left right output final := by
    apply entry_prepare program 0 prepare (addOverflowEntryBody profile finish prepare) profile avx512 28
      entryFound rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl prepareContract features memory entered left right
      output frame call setup homes
    intro after state
    exact overflow_tail program profile avx512 finish prepare entryFound finishContract features memory entered
      after left right output frame call owned state
  obtain ⟨fuel, final, values, ran, flag, value, access, footprint⟩ := finished
  subst flag
  refine ⟨fuel, final, ?_, value, access, footprint⟩
  simpa only [overflowFlag, decide_eq_true_eq] using certify_invocation program 0 _ _ memory frame entered fuel
    final _ entryFound (binary_checked call) setup live ran

/-- Public AVX2 `Add`: wrapped sum of the initial operands, checked return, writable output, caller bytes kept. -/
theorem add_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (entryFound : program[0]? = some (addEntryBody profile 1 3))
    (finishFound : program[1]? = some (finishAddBody profile 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (prepareFound : program[3]? = some (prepareAddBody profile avx512))
    (features : AddProfile profile avx512) :
    WrappingBinaryContract (· + ·) program 0 :=
  add_contract_of_callees program profile avx512 1 3 entryFound
    (finish_contract program 1 2 profile avx512 finishFound lookupFound features)
    (prepare_contract program 3 profile avx512 prepareFound features) features

/-- Public AVX2 `AddOverflow`: exact initial-operand carry, wrapped sum, writable output, caller bytes kept. -/
theorem add_overflow_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (entryFound : program[0]? = some (addOverflowEntryBody profile 1 3))
    (finishFound : program[1]? = some (finishAddBody profile 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (prepareFound : program[3]? = some (prepareAddBody profile avx512))
    (features : AddProfile profile avx512) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program 0 :=
  add_overflow_contract_of_callees program profile avx512 1 3 entryFound
    (finish_contract program 1 2 profile avx512 finishFound lookupFound features)
    (prepare_contract program 3 profile avx512 prepareFound features) features

#print axioms add_contract_of_callees
#print axioms add_overflow_contract_of_callees
#print axioms add_contract
#print axioms add_overflow_contract
end UInt256Proof.Add.Vector256
