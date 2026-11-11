import CIL.Safety.Segment
import CIL.Safety.MethodContract
import CIL.Safety.Equations
import UInt256.Methods.Add.Vector128ArithmeticDefinitions
import UInt256.Safety.OutputAccess
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessSlices
import CIL.Safety.AccessBelow
import CIL.SIMD.EvaluationLemmas
import CIL.Safety.StepComposition
import CIL.Safety.NumericHomes
import UInt256.Safety.NumericStore
import UInt256.Safety.HalfAccess
import CIL.SIMD.Incoming128
import CIL.Safety.GuardNormalization

/-!
Add and Subtract share the Vector128 prefix that saves both operands' halves in private vector
homes before any arithmetic or caller output write, and the facts about those homes.
-/

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety
/-- The reference root may change while the numeric homes retain their addresses. -/
theorem vector128_local_store (program : CIL.Program) (body : CIL.Method) (specs : List NumericLocalSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec)
    (specified : specs[index]? = some spec)
    (value : CIL.Value) (number : Nat)
    (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index + 1]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 =
        .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step body (.setLocal (index + 1)) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.home_at index spec specified
  have actual : frame.locals[index + 1]? = some (.bytes spec.kind reference) := by
    simpa [layout] using slot
  obtain ⟨after, result⟩ := checked_numeric_home_store program body boundary
    entered current inputs outputs frame currentCall enteredWF authority (index + 1)
    spec reference actual bound writable value number fits
  exact ⟨reference, after, actual, result⟩

/-- Private writes preserve the initial operand halves, including when caller operands overlap each other or the output. -/
theorem vector128_input_load (program : CIL.Program) (original current : Memory)
    (inputs outputs : List Reference) (input : Reference) (half : Fin 2)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : input ∈ inputs)
    (preserved : MemoryBelow original.nextIdentity original current) :
    loadValue current (.address { input with offset := input.offset + 16 * half.val }) 16 =
      .ok (.v128 (inputHalf original input half)) := by
  rw [currentCall.input_half_load member half]
  simp only [inputHalf, call.input_bytes_of_memory_below preserved member]

/-- A write to a later private home preserves an earlier snapshot. -/
theorem vector128_prior_read (specs : List NumericLocalSpec) (entered before after : Memory) (boundary : Nat)
    (slots : List LocalSlot) (homes : NumericHomes entered boundary specs slots)
    (i j : Nat) (earlier : i < j) (source target : Reference)
    (sourceSlot : slots[i]? = some (.bytes .vector128 source))
    (targetSlot : slots[j]? = some (.bytes .vector128 target))
    (bytes value : List (BitVec 8))
    (written : write before target bytes 1 = .ok after)
    (loaded : read before source 16 1 = .ok value) :
    read after source 16 1 = .ok value := by
  have ordered := homes.ordered i j .vector128 .vector128 source target earlier sourceSlot targetSlot
  exact write_preserves_disjoint_read written loaded (Or.inl (Nat.ne_of_lt ordered))

def vector128PrefixCode : List CIL.Op := [
  .arg 0, .memory .asRef, .memory .asRef, .arg 1, .memory .asRef, .memory .asRef, .setLocal 0,
  .dup, .memory .load128, .setLocal 1,
  .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 2,
  .local 0, .memory .load128, .setLocal 3,
  .local 0, .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 4]

def vector128ZeroSpec : NumericLocalSpec := ⟨.vector128, .v128 0, 0, rfl⟩

def vector128SavedFrame (frame : Frame) (slots : List LocalSlot) (right : Reference) : Frame :=
  { frame with locals := .root (some (.address right)) :: slots }

/-- The first `done` private vector homes hold the saved values `value`. -/
abbrev VectorSnapshots (memory : Memory) (slots : List LocalSlot) (value : Nat → BitVec 128)
    (done : Nat) : Prop :=
  ∀ i, i < done → ∃ reference, slots[i]? = some (.bytes .vector128 reference) ∧
    read memory reference 16 1 = .ok (numberBytes (value i).toNat 16)

/-- Caller views and saved private vectors while a Vector128 helper runs. Storage of `base`
    below `boundary` is intact, so facts about `base` survive every private store. -/
structure VectorState (program : CIL.Program) (boundary : Nat) (base entered current : Memory)
    (inputs outputs : List Reference) (slots : List LocalSlot) (value : Nat → BitVec 128)
    (done : Nat) : Prop where
  call : CallingConditions program current inputs outputs
  preserved : MemoryBelow boundary base current
  authority : AccessBelow entered.nextIdentity entered current
  advanced : entered.nextIdentity ≤ current.nextIdentity
  snapshots : VectorSnapshots current slots value done

/-- Storing the next saved value keeps every earlier private snapshot and all caller facts. -/
theorem VectorState.store {program : CIL.Program} {boundary : Nat} {base entered current : Memory}
    {inputs outputs : List Reference} {slots : List LocalSlot} {value : Nat → BitVec 128}
    {done : Nat}
    (state : VectorState program boundary base entered current inputs outputs slots value done)
    (body : CIL.Method) (specs : List NumericLocalSpec) (frame : Frame) (root : LocalSlot)
    (layout : frame.locals = root :: slots) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (specified : specs[done]? = some vector128ZeroSpec) (stored : BitVec 128)
    (same : value done = stored) :
    ∃ after,
      VectorState program boundary base entered after inputs outputs slots value (done + 1) ∧
      ∀ pc args rest, step body (.setLocal (done + 1)) pc args frame
        (.scalar (.v128 stored) :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨home, after, slot, loaded, retained, afterCall, afterAuthority, written, stepped⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root
      slots layout state.call enteredWF homes state.authority done vector128ZeroSpec specified
      (.v128 stored) stored.toNat rfl
  have homeSlot : slots[done]? = some (.bytes .vector128 home) := by
    simpa [layout, vector128ZeroSpec] using slot
  refine ⟨after, ⟨afterCall, state.preserved.trans retained, afterAuthority,
    Nat.le_trans state.advanced (write_extends_allocations _ _ _ _ _ written).next, ?_⟩, stepped⟩
  intro i lower
  by_cases last : i = done
  · subst last
    exact ⟨home, homeSlot, by rw [same]; exact loaded⟩
  · obtain ⟨source, sourceSlot, sourceRead⟩ := state.snapshots i (by omega)
    exact ⟨source, sourceSlot, vector128_prior_read specs entered current after boundary slots
      homes i done (by omega) source home sourceSlot homeSlot _ _ written sourceRead⟩

/-- A saved vector loads as its recorded value. -/
theorem VectorSnapshots.load {memory : Memory} {slots : List LocalSlot}
    {value : Nat → BitVec 128} {done : Nat} (snapshots : VectorSnapshots memory slots value done)
    (frame : Frame) (root : LocalSlot) (layout : frame.locals = root :: slots)
    (i : Nat) (lower : i < done) (body : CIL.Method) (pc : Nat) (args stack : List Value) :
    step body (.local (i + 1)) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar (.v128 (value i)) :: stack) frame memory) := by
  obtain ⟨home, slot, loaded⟩ := snapshots i lower
  exact step_load_numeric_local .vector128 (.v128 _) _ rfl (by simpa [layout] using slot) loaded

/-- Fresh private homes keep their snapshots across writes that spare fresh allocations. -/
theorem VectorSnapshots.transfer {entered before after : Memory} {boundary : Nat}
    {specs : List NumericLocalSpec} {slots : List LocalSlot} {value : Nat → BitVec 128}
    {done : Nat} (snapshots : VectorSnapshots before slots value done)
    (homes : NumericHomes entered boundary specs slots)
    (kept : ∀ reference, boundary ≤ reference.allocation → ∀ bytes,
      read before reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) :
    VectorSnapshots after slots value done := by
  intro i lower
  obtain ⟨home, slot, loaded⟩ := snapshots i lower
  exact ⟨home, slot, kept home (homes.home_bound i .vector128 home slot) _ loaded⟩

/-- Save all four initial input halves before arithmetic or caller output writes. -/
theorem vector128_inputs_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 0 vector128PrefixCode)
    (firstFour : ∀ i : Fin 4, specs[i.val]? = some vector128ZeroSpec)
    (original entered : Memory) (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (value : Nat → BitVec 128)
    (leftLow : value 0 = inputHalf original left 0)
    (leftHigh : value 1 = inputHalf original left 1)
    (rightLow : value 2 = inputHalf original right 0)
    (rightHigh : value 3 = inputHalf original right 1)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program original.nextIdentity original entered after inputs outputs slots
        value 4 →
      ∃ fuel result returned,
        run program fuel method 22 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredCall := call.after_frame_setup setup
  have store := fun current done (state : VectorState program original.nextIdentity original
      entered current inputs outputs slots value done) (declared : done < 4) stored same =>
    state.store body specs (vector128SavedFrame frame slots right) _ rfl enteredCall.1.1 homes
      (firstFour ⟨done, declared⟩) stored same
  obtain ⟨m0, s0, store0⟩ := store entered 0 ⟨enteredCall,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup, (MemoryBelow.refl _ _).accessBelow,
    Nat.le_refl _, fun _ lower => absurd lower (Nat.not_lt_zero _)⟩ (by decide) _ leftLow
  obtain ⟨m1, s1, store1⟩ := store m0 1 s0 (by decide) _ leftHigh
  obtain ⟨m2, s2, store2⟩ := store m1 2 s1 (by decide) _ rightLow
  obtain ⟨m3, s3, store3⟩ := store m2 3 s2 (by decide) _ rightHigh
  have load := fun current (currentCall : CallingConditions program current inputs outputs)
      (kept : MemoryBelow original.nextIdentity original current) input member half =>
    vector128_input_load program original current inputs outputs input half call currentCall
      member kept
  have load0 := load entered enteredCall (enterFrame_preserves_caller_memory _ _ _ _ _ setup)
    left leftMember 0
  have load1 := load m0 s0.call s0.preserved left leftMember 1
  have load2 := load m1 s1.call s1.preserved right rightMember 0
  have load3 := load m2 s2.call s2.preserved right rightMember 1
  have upperLeft := s0.call.input_half_address leftMember 1
  have upperRight := s2.call.input_half_address rightMember 1
  have rightRoot : (vector128SavedFrame frame slots right).locals[0]? =
      some (.root (some (.address right))) := rfl
  cil_contract_steps [found, code, layout, leftArg, rightArg, vector128SavedFrame,
    enteredCall.input_formed leftMember, enteredCall.input_formed rightMember,
    s1.call.input_formed rightMember, s2.call.input_formed rightMember, rightRoot,
    load0, load1, load2, load3, upperLeft, upperRight, store0, store1, store2,
    store3] until continuation m3 s3

/-- Overwriting any private vector home preserves every other vector home. -/
theorem vector128_other_read (specs : List NumericLocalSpec) (entered before after : Memory) (boundary : Nat)
    (slots : List LocalSlot) (homes : NumericHomes entered boundary specs slots)
    (i j : Nat) (different : i ≠ j) (source target : Reference)
    (sourceSlot : slots[i]? = some (.bytes .vector128 source))
    (targetSlot : slots[j]? = some (.bytes .vector128 target))
    (bytes value : List (BitVec 8))
    (written : write before target bytes 1 = .ok after)
    (loaded : read before source 16 1 = .ok value) :
    read after source 16 1 = .ok value := by
  by_cases earlier : i < j
  · exact vector128_prior_read specs entered before after boundary slots homes i j earlier
      source target sourceSlot targetSlot bytes value written loaded
  · have ordered := homes.ordered j i .vector128 .vector128 target source (by omega) targetSlot sourceSlot
    exact write_preserves_disjoint_read written loaded (Or.inl (Nat.ne_of_gt ordered))

end UInt256Proof.AddSubtract.Safety

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety
/-- The extracted reference root remains distinct from initialized numeric homes. -/
theorem vector128_frame_setup (body : CIL.Method) (specs : List NumericLocalSpec)
    (metadata : body.localKinds = .reference :: specs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: specs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (opaqueLocals : body.opaqueVectorLocals = [])
    (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered slots,
      enterFrame body args memory = .ok (frame, entered) ∧
      frame.locals = .root (some .null) :: slots ∧
      NumericHomes entered memory.nextIdentity specs slots ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity specs wf
  simp only [numericKinds, numericInitializers] at made
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := .root (some .null) :: slots
        owned := owned
        arguments := []
        stackBytes := 0 }

  have setup : enterFrame body args memory = .ok (frame, entered) := by
    simp only [enterFrame, metadata.1, metadata.2,
      opaqueLocals, makeSelectedLocals, List.isEmpty_nil, ite_true, makeLocals, makeLocal, made, vectors, makeArgumentHomes, parameters, makeParameterHomes,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.nil_append, List.append_nil, List.map_nil]
    rfl
  exact ⟨frame, entered, slots, setup, rfl, homes,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup,
    enterFrame_preserves_wellFormed _ _ _ _ _ wf setup⟩

end UInt256Proof.AddSubtract.Safety
