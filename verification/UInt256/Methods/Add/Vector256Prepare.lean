import CIL.Safety.Equations
import UInt256.Methods.Add.Vector256Finish
import UInt256.Methods.Add.Vector256Math
import CIL.Safety.Certificate

namespace UInt256Proof.Add.Vector256
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety

def prepareArguments (left right output s0 s1 s2 s3 : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output),
   .reference (.address s0), .reference (.address s1), .reference (.address s2), .reference (.address s3)]

def prepareSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩]

def inputLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (fun _ => none) 0 (.v256 left)) 1 (.v256 right)

/-- The lane sums written to the first scratch cell. -/
def inputCells (left right : BitVec 256) : Nat → Option (BitVec 256) :=
  rememberCell (fun _ => none) 0 (CIL.Vector.zip256 (· + ·) left right)

/-- Lane sums, generated carries and their incoming shift. -/
def maskCells (left right : BitVec 256) : Nat → Option (BitVec 256) :=
  rememberCell (rememberCell (inputCells left right) 1 (generatedCarry left right)) 2
    (incomingCarry (generatedCarry left right))

/-- All four values `PrepareAdd` returns through its reference arguments. -/
def preparedCells (left right : BitVec 256) : Nat → Option (BitVec 256) :=
  rememberCell (maskCells left right) 3 (propagationMask (CIL.Vector.zip256 (· + ·) left right))

/-- The speculative sum `PrepareAdd` stores: lane sums plus each incoming carry. -/
def fastSum (left right : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (· - ·) (CIL.Vector.zip256 (· + ·) left right) (incomingCarry (generatedCarry left right))

/-- AVX2 `PrepareAdd` that forms the incoming carries with a permute and a constant lane mask. -/
def Masked.prepareMaskedBody (profile : CIL.FeatureProfile) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize (← `(
    let template := prepareAddBody $(Lean.mkIdent `profile) false
    let mask : List CIL.Op := [.const32 0, .convI8,
      .const32 (BitVec.ofInt 32 (-1)), .convI8, .const32 (BitVec.ofInt 32 (-1)), .convI8,
      .const32 (BitVec.ofInt 32 (-1)), .convI8,
      .intrinsic (.vector (.create64 256)) 4, .intrinsic (.vector (.band 256)) 2]
    { template with code := template.code.take 46 ++ mask ++ template.code.drop 51 })) none
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce body)

theorem Masked.masked_incoming (mask : BitVec 256) :
    CIL.Vector.permute4x64 mask (BitVec.ofNat 8 144) &&&
      CIL.Vector.pack256 (BitVec.ofNat 64 0) (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 18446744073709551615) =
      incomingCarry mask := by
  rw [UInt256Proof.Subtract.Vector256.permute_incoming, ← CIL.Vector.pack256_lanes mask, incomingCarry_packed,
    UInt256Proof.Subtract.Vector256.incoming_packed]

/-- `PrepareAdd`, extracted or with the masked permute: speculative sum in the output, lane
    vectors in the caller cells, other caller bytes kept. -/
theorem prepare_invoke (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (body : CIL.Method)
    (variant : body = prepareAddBody profile avx512 ∨
      avx512 = false ∧ body = Masked.prepareMaskedBody profile)
    (found : program[method]? = some body) (features : AddProfile profile avx512)
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
  obtain ⟨kinds, initializers, vectorArgs, parameterHomes, opaqueLocals, profileEq⟩ :
      body.localKinds = prepareSpecs.map NumericLocalSpec.kind ∧
        body.locals = prepareSpecs.map NumericLocalSpec.value ∧ body.vectorArgs = [] ∧
        body.parameterHomes = [] ∧ body.opaqueVectorLocals = [] ∧ body.profile = profile := by
    rcases variant with rfl | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨frame, entered, setup, numeric, below, _⟩ := numeric_frame_setup
    body prepareSpecs kinds initializers vectorArgs parameterHomes opaqueLocals memory args call.1.1
  have homes := CIL.Safety.NumericHomes.complete numeric
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
    have facts {known stored values current}
        (state : VectorFrame program original entered current [left, right] output frame known
          stored) (cells : ScratchCells current [s0, s1, s2, s3] values) :
        form current left = .ok left ∧ form current right = .ok right ∧
          form current output = .ok output ∧ form current s0 = .ok s0 ∧ form current s1 = .ok s1 ∧
          form current s2 = .ok s2 ∧ form current s3 = .ok s3 ∧ profile.avx = true ∧
          profile.avx2 = true ∧ profile.avx512F = avx512 ∧ profile.avx512FVL = avx512 :=
      ⟨state.call.input_formed (by simp), state.call.input_formed (by simp),
        state.call.output_formed (by simp), access_reference_valid _ _ _ _ _ (cells 0 s0 rfl).1,
        access_reference_valid _ _ _ _ _ (cells 1 s1 rfl).1,
        access_reference_valid _ _ _ _ _ (cells 2 s2 rfl).1,
        access_reference_valid _ _ _ _ _ (cells 3 s3 rfl).1, features.avx, features.avx2,
        features.wideF, features.wide⟩
    suffices inputs : ∀ current,
        VectorFrame program original entered current [left, right] output frame (fun _ => none)
          none → ScratchCells current [s0, s1, s2, s3] (fun _ => none) →
        ∃ fuel final returned, run program fuel method 0 args frame [] current =
          .ok (final, returned) ∧ post final returned from
      inputs entered (.initial_from call grown same setup) (scratch.after_below below cellsOld)
    intro current state cells
    have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call
      (by simp : left ∈ [left, right])
    have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input current left
    rw [state.input_value originalCall (by simp : left ∈ [left, right])] at castLeft
    obtain ⟨enteredFormed, formed, authority, valid, preserved⟩ :=
      state.walk_facts memory.nextIdentity
    -- The extracted body steps under either AVX-512 choice; the masked body has none.
    cases avx512 <;> rcases variant with rfl | ⟨⟨⟩, rfl⟩
    all_goals
      cil_contract_steps (snapshots := state.locals) [found, args, prepareArguments, profileEq,
        facts state cells, CIL.FeatureProfile.evaluate, loadLeft, castLeft]
      replace cells := cells.after_below localBelow cellsOld
      replace state := state.after_stores originalCall localSnapshots
      have loadRight := UInt256Proof.Equality.VectorPrimitive.load_input state.call
        (by simp : right ∈ [left, right])
      have castRight := UInt256Proof.Equality.VectorPrimitive.cast_input storedLocal right
      rw [state.input_value originalCall (by simp : right ∈ [left, right])] at castRight
      cil_contract_steps (snapshots := state.locals) [found, args, prepareArguments, profileEq,
        facts state cells, CIL.FeatureProfile.evaluate, loadRight, castRight]
      replace cells := cells.after_below localBelow_1 cellsOld
      replace state := state.after_stores originalCall localSnapshots_1
      cil_contract_steps (snapshots := state.locals) [found, args, prepareArguments, profileEq,
        facts state cells, CIL.FeatureProfile.evaluate]
      refine state.run_cell_store post cells originalCall homes layout 0 found
        fun current state cells => ?_
      cil_contract_steps (snapshots := state.locals) [found, args, prepareArguments, profileEq,
        facts state cells, CIL.FeatureProfile.evaluate, (cells 0 s0 rfl).2 _ rfl]
      try rw [ternary_carry_lanes]
      refine state.run_cell_store post cells originalCall homes layout 1 found
        fun current state cells => ?_
      cil_contract_steps (snapshots := state.locals) [found, args, prepareArguments, profileEq,
        facts state cells, CIL.FeatureProfile.evaluate, (cells 1 s1 rfl).2 _ rfl]
      try rw [show CIL.Vector.alignRight64 (generatedCarry a b) 0 3 =
        incomingCarry (generatedCarry a b) from align_carry _]
      try rw [Masked.masked_incoming]
      refine state.run_cell_store post cells originalCall homes layout 2 found
        fun current state cells => ?_
      cil_contract_steps (snapshots := state.locals) [found, args, prepareArguments, profileEq,
        facts state cells, CIL.FeatureProfile.evaluate, (cells 0 s0 rfl).2 _ rfl,
        (cells 2 s2 rfl).2 _ rfl]
      refine state.run_output_store post cells originalCall (homes.weaken grown) layout found
        fun current state cells => ?_
      cil_contract_steps (snapshots := state.locals) [found, args, prepareArguments, profileEq,
        facts state cells, CIL.FeatureProfile.evaluate, (cells 0 s0 rfl).2 _ rfl]
      refine state.run_cell_store post cells originalCall homes layout 3 found
        fun current state cells => ?_
      cil_contract_steps [found]
      have retained := leaveFrame_preserves_memory_below frame current memory.nextIdentity owned
      obtain ⟨_, _, footprint⟩ := state.finish originalCall ownedOriginal
      refine ⟨rfl, fun world => ?_, ?_, footprint, state.finish_read originalCall ownedOriginal,
        ScratchCells.after_below cells retained cellsOld⟩
      · exact CallingConditions.retained originalCall state.call
          (leaveFrame_preserves_memory_below frame current original.nextIdentity ownedOriginal)
          (leaveFrame_preserves_wellFormed frame current state.call.1.1) world
      · exact (below.accessBelow.trans (state.authority.weaken enteredGrown)).trans
          retained.accessBelow
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

/-- What a compiled `PrepareAdd` guarantees its caller, independent of its body. -/
def PrepareContract (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (original memory : Memory) (left right output s0 s1 s2 s3 : Reference),
    CallingConditions program original [left, right] [output] →
    CallingConditions program memory [left, right] [output] →
    original.nextIdentity ≤ memory.nextIdentity →
    (∀ id, id < original.nextIdentity → ∀ offset, memory.cells id offset = original.cells id offset) →
    ScratchLayout original.nextIdentity memory.nextIdentity [s0, s1, s2, s3] →
    ScratchCells memory [s0, s1, s2, s3] (fun _ => none) →
    ∃ fuel after,
      invoke program fuel method (prepareArguments left right output s0 s1 s2 s3) memory = .ok (after, []) ∧
      CallingConditions program after [left, right] [output] ∧
      memory.nextIdentity ≤ after.nextIdentity ∧ AccessBelow memory.nextIdentity memory after ∧
      (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) ∧
      CIL.Safety.read after output 32 1 =
        .ok (numberBytes (fastSum (inputValue original left) (inputValue original right)).toNat 32) ∧
      ScratchCells after [s0, s1, s2, s3] (preparedCells (inputValue original left) (inputValue original right))

theorem prepare_contract (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareAddBody profile avx512)) (features : AddProfile profile avx512) :
    PrepareContract program method :=
  fun original memory left right output s0 s1 s2 s3 originalCall call grown same layout scratch =>
    prepare_invoke program method profile avx512 _ (.inl rfl) found features original memory left
      right output s0 s1 s2 s3 originalCall call grown same layout scratch

end UInt256Proof.Add.Vector256
