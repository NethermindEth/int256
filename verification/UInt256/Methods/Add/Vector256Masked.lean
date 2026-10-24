import UInt256.Methods.Add.Vector256Entry

namespace UInt256Proof.Add.Vector256.Masked
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety UInt256Proof.Add.Vector256
variable {identity : Nat} {assembly : String}

/-- AVX2 `PrepareAdd` that forms the incoming carries with a permute and a constant lane mask. -/
def prepareMaskedBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := false, locals := [.v256 0, .v256 0], localKinds := [.vector256, .vector256], parameterHomes := [], staticSites := [], code := [
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
  .brzero 35,
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
  .arg 4,
  .arg 3,
  .memory .load256,
  .local 0,
  .intrinsic (.vector (.ltu64 256)) 2,
  .memory .store256,
  .arg 5,
  .arg 4,
  .memory .load256,
  .const32 (BitVec.ofInt 32 (144)),
  .intrinsic (.avx2 .permute4x64) 2,
  .const32 0,
  .convI8,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .const32 (BitVec.ofInt 32 (-1)),
  .convI8,
  .intrinsic (.vector (.create64 256)) 4,
  .intrinsic (.vector (.band 256)) 2,
  .memory .store256,
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

theorem masked_incoming (mask : BitVec 256) :
    CIL.Vector.permute4x64 mask (BitVec.ofNat 8 144) &&&
      CIL.Vector.pack256 (BitVec.ofNat 64 0) (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 18446744073709551615) =
      incomingCarry mask := by
  rw [UInt256Proof.Subtract.Vector256.permute_incoming, ← CIL.Vector.pack256_lanes mask, incomingCarry_packed,
    UInt256Proof.Subtract.Vector256.incoming_packed]

#print axioms masked_incoming

theorem prepare_inputs (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (prepareMaskedBody profile)) (features : AddProfile profile false)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareMaskedBody profile).localKinds frame.locals)
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
  have profileEq : (prepareMaskedBody profile).profile = profile := rfl
  have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : left ∈ [left, right])
  have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input current left
  have sameLeft := state.input_value originalCall (by simp : left ∈ [left, right])
  rw [sameLeft] at castLeft
  prep_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, pureArity, loadLeft]; rfl
  apply run_next_exists post found (by rfl)
  · simp only [step, cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, staticInstruction, castLeft]; rfl
  prep_store
  have loadRight := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : right ∈ [left, right])
  have castRight := UInt256Proof.Equality.VectorPrimitive.cast_input current right
  have sameRight := state.input_value originalCall (by simp : right ∈ [left, right])
  rw [sameRight] at castRight
  prep_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, pureArity, loadRight]; rfl
  apply run_next_exists post found (by rfl)
  · simp only [step, cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, staticInstruction, castRight]; rfl
  prep_store
  prep_pure
  prep_load
  prep_load
  prep_pure
  apply VectorFrame.run_cell_store post state scratch originalCall homes layout 0 rfl found (by rfl)
  intro current state scratch
  exact continuation current state scratch

#print axioms prepare_inputs

theorem prepare_masks (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (prepareMaskedBody profile)) (features : AddProfile profile false)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareMaskedBody profile).localKinds frame.locals)
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
        run program fuel method 57 (prepareArguments left right output s0 s1 s2 s3) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 13 (prepareArguments left right output s0 s1 s2 s3) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (prepareMaskedBody profile).profile = profile := rfl
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
  prep_pure
  prep_pure
  prep_pure
  prep_pure
  prep_pure
  rw [masked_incoming]
  apply VectorFrame.run_cell_store post state scratch originalCall homes layout 2 rfl found (by rfl)
  intro current state scratch
  exact continuation current state scratch

#print axioms prepare_masks

theorem prepare_tail (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (prepareMaskedBody profile)) (features : AddProfile profile false)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareMaskedBody profile).localKinds frame.locals)
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
      run program fuel method 57 (prepareArguments left right output s0 s1 s2 s3) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (prepareMaskedBody profile).profile = profile := rfl
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
  have returns : (prepareMaskedBody profile).returnsValue = false := rfl
  have fetched : (prepareMaskedBody profile).code[73]? = some .ret := rfl
  refine ⟨1, _, _, ?_, continuation current state scratch⟩
  simp [run, found, fetched, returns, step, cil_guard, observerCount, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms prepare_tail

/-- `PrepareAdd`: speculative sum in the output, lane vectors in the caller cells, other caller bytes kept. -/
theorem prepare_invoke (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (prepareMaskedBody profile)) (features : AddProfile profile false)
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
    (prepareMaskedBody profile) prepareSpecs rfl rfl rfl rfl rfl memory args call.1.1
  have homes : WritableHomes entered memory.nextIdentity
      (prepareMaskedBody profile).localKinds frame.locals :=
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
    apply prepare_inputs program method profile found features original memory entered entered
      left right output s0 s1 s2 s3 frame originalCall homes grown layout
      (VectorFrame.initial_from call grown same setup) (ScratchCells.after_below scratch below cellsOld) post
    intro current state cells
    apply prepare_masks program method profile found features original memory entered current
      left right output s0 s1 s2 s3 frame originalCall homes grown layout a b state cells post
    intro current state cells
    apply prepare_tail program method profile found features original memory entered current
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

theorem prepare_contract (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (prepareMaskedBody profile)) (features : AddProfile profile false) :
    PrepareContract program method :=
  fun original memory left right output s0 s1 s2 s3 originalCall call grown same layout scratch =>
    prepare_invoke program method profile found features original memory left right output s0 s1 s2 s3
      originalCall call grown same layout scratch

#print axioms prepare_contract

/-- AVX2 `Add` whose `PrepareAdd` masks the permuted carries with a constant lane mask. -/
theorem add_contract (program : CIL.Program) (profile : CIL.FeatureProfile)
    (entryFound : program[0]? = some (addEntryBody profile 1 3))
    (finishFound : program[1]? = some (finishAddBody profile 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (prepareFound : program[3]? = some (prepareMaskedBody profile))
    (features : AddProfile profile false) :
    WrappingBinaryContract (· + ·) program 0 :=
  add_contract_of_callees program profile false 1 3 entryFound
    (finish_contract program 1 2 profile false finishFound lookupFound features)
    (prepare_contract program 3 profile prepareFound features) features

/-- AVX2 `AddOverflow` whose `PrepareAdd` masks the permuted carries with a constant lane mask. -/
theorem add_overflow_contract (program : CIL.Program) (profile : CIL.FeatureProfile)
    (entryFound : program[0]? = some (addOverflowEntryBody profile 1 3))
    (finishFound : program[1]? = some (finishAddBody profile 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (prepareFound : program[3]? = some (prepareMaskedBody profile))
    (features : AddProfile profile false) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program 0 :=
  add_overflow_contract_of_callees program profile false 1 3 entryFound
    (finish_contract program 1 2 profile false finishFound lookupFound features)
    (prepare_contract program 3 profile prepareFound features) features

#print axioms add_contract
#print axioms add_overflow_contract
end UInt256Proof.Add.Vector256.Masked
