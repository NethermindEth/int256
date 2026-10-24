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

set_option hygiene false in
/-- One pure instruction of `PrepareAdd`; expects `post found features profileEq state scratch` and the references. -/
macro "prep_pure" : tactic => `(tactic|
  (have formedLeft := state.call.input_formed (reference := left) (by simp)
   have formedRight := state.call.input_formed (reference := right) (by simp)
   have formedOutput := state.call.output_formed (reference := output) (by simp)
   have formed0 := access_reference_valid _ _ _ _ _ (scratch 0 s0 rfl).1
   have formed1 := access_reference_valid _ _ _ _ _ (scratch 1 s1 rfl).1
   have formed2 := access_reference_valid _ _ _ _ _ (scratch 2 s2 rfl).1
   have formed3 := access_reference_valid _ _ _ _ _ (scratch 3 s3 rfl).1
   apply run_next_exists post found (by rfl)
   · simp (config := { implicitDefEqProofs := false })
       [step, cil_guard, observerCount, pureArity, prepareArguments, checkedValue, numericValue, formValue, formedLeft, formedRight,
         formedOutput, formed0, formed1, formed2, formed3, staticInstruction, memoryInstruction, checkedAt,
         profileEq, features.avx, features.avx2, features.wideF, features.wide, CIL.FeatureProfile.evaluate,
         scalars, checkedIntrinsic, CIL.Intrinsic.available, CIL.step.eq_def, CIL.binary, CIL.unary, CIL.truth,
         instruction, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
     try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

set_option hygiene false in
macro "prep_store" : tactic => `(tactic|
  (apply VectorFrame.run_store_scratch post state scratch originalCall homes bound layout found
     (by rfl) (by rfl) (by rfl) (by rfl)
   intro current state scratch))

set_option hygiene false in
macro "prep_load" : tactic => `(tactic|
  apply VectorFrame.run_load post state found (by rfl) (by rfl))

theorem prepare_inputs (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareAddBody profile avx512)) (features : AddProfile profile avx512)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareAddBody profile avx512).localKinds frame.locals)
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
  have profileEq : (prepareAddBody profile avx512).profile = profile := rfl
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

theorem prepare_masks (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareAddBody profile avx512)) (features : AddProfile profile avx512)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareAddBody profile avx512).localKinds frame.locals)
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
        run program fuel method 52 (prepareArguments left right output s0 s1 s2 s3) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 13 (prepareArguments left right output s0 s1 s2 s3) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (prepareAddBody profile avx512).profile = profile := rfl
  cases avx512
  · prep_pure
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
    (found : program[method]? = some (prepareAddBody profile avx512)) (features : AddProfile profile avx512)
    (original memory entered current : Memory) (left right output s0 s1 s2 s3 : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered memory.nextIdentity (prepareAddBody profile avx512).localKinds frame.locals)
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
      run program fuel method 52 (prepareArguments left right output s0 s1 s2 s3) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (prepareAddBody profile avx512).profile = profile := rfl
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
  have returns : (prepareAddBody profile avx512).returnsValue = false := rfl
  have fetched : (prepareAddBody profile avx512).code[68]? = some .ret := rfl
  refine ⟨1, _, _, ?_, continuation current state scratch⟩
  simp [run, found, fetched, returns, step, cil_guard, observerCount, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms prepare_tail

/-- `PrepareAdd`: speculative sum in the output, lane vectors in the caller cells, other caller bytes kept. -/
theorem prepare_invoke (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (prepareAddBody profile avx512)) (features : AddProfile profile avx512)
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
    (prepareAddBody profile avx512) prepareSpecs rfl rfl rfl rfl rfl memory args call.1.1
  have homes : WritableHomes entered memory.nextIdentity
      (prepareAddBody profile avx512).localKinds frame.locals :=
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
    prepare_invoke program method profile avx512 found features original memory left right output s0 s1 s2 s3
      originalCall call grown same layout scratch

#print axioms prepare_contract
end UInt256Proof.Add.Vector256
