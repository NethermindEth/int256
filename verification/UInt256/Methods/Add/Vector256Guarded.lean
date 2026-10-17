import UInt256.Methods.Add.Vector256Entry

namespace UInt256Proof.Add.Vector256.Guarded
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety UInt256Proof.Add.Vector256

/-- `PrepareAdd` with the AVX512VL test conjoined with an implied AVX test. -/
def prepareGuardedBody (profile : CIL.FeatureProfile) (avx512 : Bool) : CIL.Method := { profile := profile, returnsValue := false, locals := [.v256 0, .v256 0], localKinds := [.vector256, .vector256], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .setLocal 0,
  .arg 1,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .setLocal 1,
  .arg 3,
  .local 0,
  .local 1,
  .intrinsic (.vector (.add64 256)) 2,
  .memory .store256,
  .feature .avx512FVL,
  .feature .avx,
  .band,
  .brzero 37,
  (if avx512 then .arg 4 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .local 0 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .local 1 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .arg 3 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .memory .load256 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .const32 (BitVec.ofInt 32 (212)) else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.avx512 .ternaryLogic) 4 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .const32 (BitVec.ofInt 32 (63)) else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.ashr64 256)) 2 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .memory .store256 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .arg 5 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .arg 4 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .memory .load256 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.zero 256)) 0 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .const32 3 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.avx512 .alignRight64) 3 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .memory .store256 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .branch 54 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .unsupported "Unreachable under selected profile" else .arg 4),
  (if avx512 then .unsupported "Unreachable under selected profile" else .arg 3),
  (if avx512 then .unsupported "Unreachable under selected profile" else .memory .load256),
  (if avx512 then .unsupported "Unreachable under selected profile" else .local 0),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.vector (.ltu64 256)) 2),
  (if avx512 then .unsupported "Unreachable under selected profile" else .memory .store256),
  (if avx512 then .unsupported "Unreachable under selected profile" else .arg 5),
  (if avx512 then .unsupported "Unreachable under selected profile" else .arg 4),
  (if avx512 then .unsupported "Unreachable under selected profile" else .memory .load256),
  (if avx512 then .unsupported "Unreachable under selected profile" else .const32 (BitVec.ofInt 32 (144))),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.avx2 .permute4x64) 2),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.vector (.reinterpret 256)) 1),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.vector (.zero 256)) 0),
  (if avx512 then .unsupported "Unreachable under selected profile" else .const32 3),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.avx2 .blend32) 3),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.vector (.reinterpret 256)) 1),
  (if avx512 then .unsupported "Unreachable under selected profile" else .memory .store256),
  .arg 2,
  .skipInit,
  .arg 2,
  .memory .asRef,
  .arg 3,
  .memory .load256,
  .arg 5,
  .memory .load256,
  .intrinsic (.vector (.sub64 256)) 2,
  .memory .store256,
  .arg 6,
  .arg 3,
  .memory .load256,
  .intrinsic (.vector (.ones 256)) 0,
  .intrinsic (.vector (.eq64 256)) 2,
  .memory .store256,
  .ret] }

theorem prepare_inputs (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareGuardedBody profile avx512)) (features : AddProfile profile avx512)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareGuardedBody profile avx512).localKinds frame.locals)
    (bound : original.nextIdentity ≤ memory.nextIdentity)
    (layout : ScratchLayout original.nextIdentity memory.nextIdentity [s0, s1, s2, s3])
    (state : VectorFrame program original entered current [left, right] output frame (fun _ => none) none)
    (scratch : ScratchCells current [s0, s1, s2, s3] (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame
        (inputLocals (inputValue original left) (inputValue original right)) none →
      ScratchCells after [s0, s1, s2, s3] (inputCells (inputValue original left) (inputValue original right)) →
      ∃ fuel final values,
        run program fuel method 13 (prepareArguments left right output s0 s1 s2 s3) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 0 (prepareArguments left right output s0 s1 s2 s3) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (prepareGuardedBody profile avx512).profile = profile := rfl
  have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : left ∈ [left, right])
  have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input current left
  have sameLeft := state.input_value originalCall (by simp : left ∈ [left, right])
  rw [sameLeft] at castLeft
  prep_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, pureArity, loadLeft]; rfl
  apply run_next_exists post found (by rfl)
  · simp only [step, staticInstruction, castLeft]; rfl
  prep_store
  have loadRight := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : right ∈ [left, right])
  have castRight := UInt256Proof.Equality.VectorPrimitive.cast_input current right
  have sameRight := state.input_value originalCall (by simp : right ∈ [left, right])
  rw [sameRight] at castRight
  prep_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, pureArity, loadRight]; rfl
  apply run_next_exists post found (by rfl)
  · simp only [step, staticInstruction, castRight]; rfl
  prep_store
  prep_pure
  prep_load
  prep_load
  prep_pure
  apply VectorFrame.run_cell_store post state scratch originalCall homes layout 0 rfl found (by rfl)
  intro current state scratch
  exact continuation current state scratch

#print axioms prepare_inputs

theorem prepare_masks (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareGuardedBody profile avx512)) (features : AddProfile profile avx512)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareGuardedBody profile avx512).localKinds frame.locals)
    (bound : original.nextIdentity ≤ memory.nextIdentity)
    (layout : ScratchLayout original.nextIdentity memory.nextIdentity [s0, s1, s2, s3])
    (a b : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (inputLocals a b) none)
    (scratch : ScratchCells current [s0, s1, s2, s3] (inputCells a b))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame (inputLocals a b) none →
      ScratchCells after [s0, s1, s2, s3] (maskCells a b) →
      ∃ fuel final values,
        run program fuel method 54 (prepareArguments left right output s0 s1 s2 s3) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 13 (prepareArguments left right output s0 s1 s2 s3) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (prepareGuardedBody profile avx512).profile = profile := rfl
  cases avx512
  · prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    apply run_cell_load post found (by rfl) ((scratch 0 s0 rfl).2 _ rfl)
    prep_load
    prep_pure
    apply VectorFrame.run_cell_store post state scratch originalCall homes layout 1 rfl found (by rfl)
    intro current state scratch
    prep_pure
    prep_pure
    apply run_cell_load post found (by rfl) ((scratch 1 s1 rfl).2 _ rfl)
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    apply VectorFrame.run_cell_store post state scratch originalCall homes layout 2 rfl found (by rfl)
    intro current state scratch
    exact continuation current state scratch
  · prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_load
    prep_load
    prep_pure
    apply run_cell_load post found (by rfl) ((scratch 0 s0 rfl).2 _ rfl)
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    prep_pure
    rw [ternary_carry_lanes]
    apply VectorFrame.run_cell_store post state scratch originalCall homes layout 1 rfl found (by rfl)
    intro current state scratch
    prep_pure
    prep_pure
    apply run_cell_load post found (by rfl) ((scratch 1 s1 rfl).2 _ rfl)
    prep_pure
    prep_pure
    prep_pure
    rw [align_carry]
    apply VectorFrame.run_cell_store post state scratch originalCall homes layout 2 rfl found (by rfl)
    intro current state scratch
    prep_pure
    exact continuation current state scratch

#print axioms prepare_masks

theorem prepare_tail (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareGuardedBody profile avx512)) (features : AddProfile profile avx512)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareGuardedBody profile avx512).localKinds frame.locals)
    (bound : original.nextIdentity ≤ memory.nextIdentity)
    (layout : ScratchLayout original.nextIdentity memory.nextIdentity [s0, s1, s2, s3])
    (a b : BitVec 256) (known : Nat → Option CIL.Value)
    (state : VectorFrame program original entered current [left, right] output frame known none)
    (scratch : ScratchCells current [s0, s1, s2, s3] (maskCells a b))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame known (some (fastSum a b)) →
      ScratchCells after [s0, s1, s2, s3] (preparedCells a b) →
      post (leaveFrame frame after) []) :
    ∃ fuel final values,
      run program fuel method 54 (prepareArguments left right output s0 s1 s2 s3) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (prepareGuardedBody profile avx512).profile = profile := rfl
  prep_pure
  prep_pure
  prep_pure
  prep_pure
  prep_pure
  apply run_cell_load post found (by rfl) ((scratch 0 s0 rfl).2 _ rfl)
  prep_pure
  apply run_cell_load post found (by rfl) ((scratch 2 s2 rfl).2 _ rfl)
  prep_pure
  apply VectorFrame.run_output_store post state scratch originalCall (homes.weaken bound) layout found (by rfl)
  intro current state scratch
  prep_pure
  prep_pure
  apply run_cell_load post found (by rfl) ((scratch 0 s0 rfl).2 _ rfl)
  prep_pure
  prep_pure
  apply VectorFrame.run_cell_store post state scratch originalCall homes layout 3 rfl found (by rfl)
  intro current state scratch
  have returns : (prepareGuardedBody profile avx512).returnsValue = false := rfl
  have fetched : (prepareGuardedBody profile avx512).code[70]? = some .ret := rfl
  refine ⟨1, _, _, ?_, continuation current state scratch⟩
  simp [run, found, fetched, returns, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms prepare_tail

/-- `PrepareAdd`: speculative sum in the output, lane vectors in the caller cells, other caller bytes kept. -/
theorem prepare_invoke (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareGuardedBody profile avx512)) (features : AddProfile profile avx512)
    (original memory : Memory) (left right output s0 s1 s2 s3 : Reference)
    (originalCall : CallingConditions program original [left, right] [output])
    (call : CallingConditions program memory [left, right] [output])
    (grown : original.nextIdentity ≤ memory.nextIdentity)
    (same : ∀ id, id < original.nextIdentity → ∀ offset, memory.cells id offset = original.cells id offset)
    (layout : ScratchLayout original.nextIdentity memory.nextIdentity [s0, s1, s2, s3])
    (scratch : ScratchCells memory [s0, s1, s2, s3] (fun _ => none)) :
    ∃ fuel after,
      invoke program fuel method (prepareArguments left right output s0 s1 s2 s3) memory = .ok (after, []) ∧
      CallingConditions program after [left, right] [output] ∧
      memory.nextIdentity ≤ after.nextIdentity ∧ AccessBelow memory.nextIdentity memory after ∧
      (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) ∧
      CIL.Safety.read after output 32 1 =
        .ok (numberBytes (fastSum (inputValue original left) (inputValue original right)).toNat 32) ∧
      ScratchCells after [s0, s1, s2, s3] (preparedCells (inputValue original left) (inputValue original right)) := by
  let args := prepareArguments left right output s0 s1 s2 s3
  let a := inputValue original left
  let b := inputValue original right
  obtain ⟨frame, entered, setup, numeric, below, _⟩ := numeric_frame_setup
    (prepareGuardedBody profile avx512) prepareSpecs rfl rfl rfl rfl memory args call.1.1
  have homes : WritableHomes entered memory.nextIdentity
      (prepareGuardedBody profile avx512).localKinds frame.locals :=
    UInt256Model.Safety.NumericHomes.writable numeric
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member =>
    ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  have ownedOriginal : ∀ id ∈ frame.owned, original.nextIdentity ≤ id := fun id member =>
    Nat.le_trans grown (owned id member)
  have enteredGrown := (enterFrame_fresh _ _ _ _ _ setup).1.next
  have cellsOld : ∀ (index : Nat) (cell : Reference), [s0, s1, s2, s3][index]? = some cell →
      cell.allocation < memory.nextIdentity := fun index cell cellFound => (layout.bounds index cell cellFound).2
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [] ∧
    (StaticWorldValid (programStaticDescriptors program) final →
      CallingConditions program final [left, right] [output]) ∧
    AccessBelow memory.nextIdentity memory final ∧
    (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = original.cells id offset) ∧
    CIL.Safety.read final output 32 1 = .ok (numberBytes (fastSum a b).toNat 32) ∧
    ScratchCells final [s0, s1, s2, s3] (preparedCells a b)
  have finished : ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧ post final returned := by
    apply prepare_inputs program method profile avx512 found features original memory entered entered
      left right output s0 s1 s2 s3 frame originalCall homes grown layout
      (VectorFrame.initial_from call grown same setup) (ScratchCells.after_below scratch below cellsOld) post
    intro current state cells
    apply prepare_masks program method profile avx512 found features original memory entered current
      left right output s0 s1 s2 s3 frame originalCall homes grown layout a b state cells post
    intro current state cells
    apply prepare_tail program method profile avx512 found features original memory entered current
      left right output s0 s1 s2 s3 frame originalCall homes grown layout a b _ state cells post
    intro current state cells
    have retained := leaveFrame_preserves_memory_below frame current memory.nextIdentity owned
    obtain ⟨_, _, footprint⟩ := state.finish originalCall ownedOriginal
    refine ⟨rfl, fun world => ?_, ?_, footprint, state.finish_read originalCall ownedOriginal,
      ScratchCells.after_below cells retained cellsOld⟩
    · exact CallingConditions.retained originalCall state.call
        (leaveFrame_preserves_memory_below frame current original.nextIdentity ownedOriginal)
        (leaveFrame_preserves_wellFormed frame current state.call.1.1) world
    · exact (below.accessBelow.trans (state.authority.weaken enteredGrown)).trans retained.accessBelow
  obtain ⟨fuel, final, returned, ran, empty, conditions, authority, footprint, result, cells⟩ := finished
  subst empty
  have formedLeft := call.input_formed (reference := left) (by simp)
  have formedRight := call.input_formed (reference := right) (by simp)
  have formedOutput := call.output_formed (reference := output) (by simp)
  have formed0 := access_reference_valid _ _ _ _ _ (scratch 0 s0 rfl).1
  have formed1 := access_reference_valid _ _ _ _ _ (scratch 1 s1 rfl).1
  have formed2 := access_reference_valid _ _ _ _ _ (scratch 2 s2 rfl).1
  have formed3 := access_reference_valid _ _ _ _ _ (scratch 3 s3 rfl).1
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, prepareArguments, checkedValue, formValue, formedLeft, formedRight, formedOutput,
      formed0, formed1, formed2, formed3, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
      Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have certificate := certify_invocation program method _ args memory frame entered fuel final []
    found checked setup live ran
  have world := certificate.2.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
  exact ⟨fuel, final, certificate.1, conditions world,
    (invoke_preserves_caller_allocations program fuel method args [] memory final certificate.1).next,
    authority, footprint, result, cells⟩

#print axioms prepare_invoke

theorem prepare_contract (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareGuardedBody profile avx512)) (features : AddProfile profile avx512) :
    PrepareContract program method :=
  fun original memory left right output s0 s1 s2 s3 originalCall call grown same layout scratch =>
    prepare_invoke program method profile avx512 found features original memory left right output s0 s1 s2 s3
      originalCall call grown same layout scratch

#print axioms prepare_contract

/-- `Add` entry with the AVX2 test conjoined with itself. -/
def addGuardedEntryBody (profile : CIL.FeatureProfile) (finish prepare : Nat) : CIL.Method := { profile := profile, returnsValue := false, locals := [.v256 0, .v256 0, .v256 0, .v256 0], localKinds := [.vector256, .vector256, .vector256, .vector256], parameterHomes := [], staticSites := [], code := [
  .feature .avx2,
  .feature .avx2,
  .band,
  .brzero 27,
  .arg 0,
  .arg 1,
  .arg 2,
  .localAddr 0,
  .localAddr 1,
  .localAddr 2,
  .localAddr 3,
  .call prepare 7,
  .local 3,
  .local 2,
  .intrinsic (.vector (.band 256)) 2,
  .intrinsic (.vector (.reinterpret 256)) 1,
  .intrinsic (.avx .moveMask64) 1,
  .const32 6,
  .band,
  .brzero 26,
  .local 0,
  .local 1,
  .local 3,
  .arg 2,
  .call finish 4,
  .pop,
  .ret,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

/-- The guarded `Add` entry up to `PrepareAdd`: the speculative sum is stored and the four lane vectors are locals. -/
theorem entry_prepare (program : CIL.Program) (finish prepare : Nat)
    (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[0]? = some (addGuardedEntryBody profile finish prepare))
    (prepareContract : PrepareContract program prepare)
    (features : AddProfile profile avx512)
    (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (setup : enterFrame (addGuardedEntryBody profile finish prepare) (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WritableHomes entered memory.nextIdentity (entrySpecs.map NumericLocalSpec.kind) frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program memory entered after [left, right] output frame
        (entryLocals (inputValue memory left) (inputValue memory right))
        (some (fastSum (inputValue memory left) (inputValue memory right))) →
      ∃ fuel final values,
        run program fuel 0 12 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel 0 0 (binaryArguments left right output) frame [] entered =
        .ok (final, values) ∧ post final values := by
  have profileEq : (addGuardedEntryBody profile finish prepare).profile = profile := rfl
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
  entry_pure
  entry_pure
  entry_address
  entry_address
  entry_address
  entry_address
  have formedLeft := state.call.input_formed (reference := left) (by simp)
  have formedRight := state.call.input_formed (reference := right) (by simp)
  have formedOutput := state.call.output_formed (reference := output) (by simp)
  have stepped : step (addGuardedEntryBody profile finish prepare) (.call prepare 7) 11 (binaryArguments left right output) frame
      [.reference (.address h3), .reference (.address h2), .reference (.address h1), .reference (.address h0),
       .reference (.address output), .reference (.address right), .reference (.address left)] entered =
      .ok (.call prepare (prepareArguments left right output h0 h1 h2 h3) [] entered) := by
    simp [step, prepareArguments, checkedValue, formValue, formedLeft, formedRight, formedOutput,
      formed0, formed1, formed2, formed3, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
      Except.pure]
  obtain ⟨total, composed⟩ := run_call_exists found rfl stepped ⟨childFuel, invoked⟩ ⟨fuel, by simpa using ran⟩
  exact ⟨total, final, values, composed, satisfied⟩

#print axioms entry_prepare

/-- The guarded `Add` entry after `PrepareAdd`: the fast return or the `FinishAdd` correction. -/
theorem add_tail (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool) (finish prepare : Nat)
    (found : program[0]? = some (addGuardedEntryBody profile finish prepare))
    (finishContract : FinishContract program finish)
    (features : AddProfile profile avx512)
    (memory entered after : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id)
    (state : VectorFrame program memory entered after [left, right] output frame
      (entryLocals (inputValue memory left) (inputValue memory right))
      (some (fastSum (inputValue memory left) (inputValue memory right)))) :
    ∃ fuel final values,
      run program fuel 0 12 (binaryArguments left right output) frame [] after = .ok (final, values) ∧
        values = [] ∧ AddPost memory left right output final := by
  have profileEq : (addGuardedEntryBody profile finish prepare).profile = profile := rfl
  let post : Memory → List Value → Prop := fun final values => values = [] ∧ AddPost memory left right output final
  have returns : (addGuardedEntryBody profile finish prepare).returnsValue = false := rfl
  have retFetch : (addGuardedEntryBody profile finish prepare).code[26]? = some .ret := rfl
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
    simp [run, found, retFetch, returns, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have selected : (CIL.Vector.moveMask64 (propagationMask (CIL.Vector.zip256 (· + ·) a b) &&&
        incomingCarry (generatedCarry a b)) &&& 6#32 != 0#32) = true := bne_iff_ne.mpr guard
    entry_branch
    simp only [selected, ↓reduceIte]
    entry_load
    entry_load
    entry_load
    entry_pure
    let sum := CIL.Vector.zip256 (· + ·) a b
    have formedOutput := state.call.output_formed (reference := output) (by simp)
    have stepped : step (addGuardedEntryBody profile finish prepare) (.call finish 4) 24 (binaryArguments left right output) frame
        [.reference (.address output), .scalar (.v256 (propagationMask sum)),
         .scalar (.v256 (generatedCarry a b)), .scalar (.v256 sum)] after =
        .ok (.call finish (finishArguments sum (generatedCarry a b) (propagationMask sum) output) [] after) := by
      simp [step, finishArguments, checkedValue, numericValue, formValue, formedOutput, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨childFuel, finished, invoked, result, writable, footprint⟩ :=
      finishContract after output state.call.without_inputs sum (generatedCarry a b) (propagationMask sum)
    obtain ⟨value, access, kept⟩ := state.finish_child call owned result writable footprint
    have popFetch : (addGuardedEntryBody profile finish prepare).code[25]? = some .pop := rfl
    have tail : run program 2 0 25 (binaryArguments left right output) frame
        ([.scalar (.i32 (finishFlag (generatedCarry a b) (propagationMask sum)))] ++ []) finished =
        .ok (leaveFrame frame finished, []) := by
      simp [run, found, popFetch, retFetch, returns, step, pureArity, instruction,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨total, ran⟩ := run_call_exists found rfl stepped ⟨childFuel, invoked⟩ ⟨2, tail⟩
    exact ⟨total, _, _, ran, rfl, by rw [ha, hb]; exact value.trans (cascade_sum_value a b), access, kept⟩

#print axioms add_tail

/-- Guarded AVX `Add` from the callee contracts: wrapped sum, checked return, writable output, caller bytes kept. -/
theorem add_contract_of_callees (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (finish prepare : Nat)
    (entryFound : program[0]? = some (addGuardedEntryBody profile finish prepare))
    (finishContract : FinishContract program finish) (prepareContract : PrepareContract program prepare)
    (features : AddProfile profile avx512) :
    WrappingBinaryContract (· + ·) program 0 := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live, homes, owned⟩ := entry_setup program (addGuardedEntryBody profile finish prepare)
    memory left right output call rfl rfl rfl rfl
  have finished : ∃ fuel final values,
      run program fuel 0 0 (binaryArguments left right output) frame [] entered = .ok (final, values) ∧
        values = [] ∧ AddPost memory left right output final := by
    apply entry_prepare program finish prepare profile avx512 entryFound prepareContract features memory entered
      left right output frame call setup homes
    intro after state
    exact add_tail program profile avx512 finish prepare entryFound finishContract features memory entered after
      left right output frame call owned state
  obtain ⟨fuel, final, values, ran, empty, value, access, footprint⟩ := finished
  subst empty
  exact ⟨fuel, final, certify_invocation program 0 _ _ memory frame entered fuel final [] entryFound
    (binary_checked call) setup live ran, value, access, footprint⟩


/-- Guarded AVX `Add`: production `FinishAdd`, guarded `PrepareAdd` and entry. -/
theorem add_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (entryFound : program[0]? = some (addGuardedEntryBody profile 1 3))
    (finishFound : program[1]? = some (finishAddBody profile 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (prepareFound : program[3]? = some (prepareGuardedBody profile avx512))
    (features : AddProfile profile avx512) :
    WrappingBinaryContract (· + ·) program 0 :=
  add_contract_of_callees program profile avx512 1 3 entryFound
    (finish_contract program 1 2 profile avx512 finishFound lookupFound features)
    (prepare_contract program 3 profile avx512 prepareFound features) features

#print axioms add_contract
end UInt256Proof.Add.Vector256.Guarded
