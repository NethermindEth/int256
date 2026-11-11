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

/-- Save all four initial input halves before arithmetic or caller output writes. -/
theorem vector128_inputs_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 0 (vector128PrefixCode))
    (firstFour : ∀ i : Fin 4, specs[i.val]? = some vector128ZeroSpec)
    (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ l0 l1 r0 r1 after,
      slots[0]? = some (.bytes .vector128 l0) →
      slots[1]? = some (.bytes .vector128 l1) →
      slots[2]? = some (.bytes .vector128 r0) →
      slots[3]? = some (.bytes .vector128 r1) →
      read after l0 16 1 = .ok (numberBytes (inputHalf original left 0).toNat 16) →
      read after l1 16 1 = .ok (numberBytes (inputHalf original left 1).toNat 16) →
      read after r0 16 1 = .ok (numberBytes (inputHalf original right 0).toNat 16) →
      read after r1 16 1 = .ok (numberBytes (inputHalf original right 1).toNat 16) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 22 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have store := fun current (currentCall : CallingConditions program current inputs outputs)
      (authority : AccessBelow entered.nextIdentity entered current) (index : Fin 4)
      (half : BitVec 128) =>
    vector128_local_store program body specs original.nextIdentity entered current inputs outputs
      (vector128SavedFrame frame slots right) _ slots rfl currentCall enteredCall.1.1 homes
      authority index.val vector128ZeroSpec (firstFour index) (.v128 half) half.toNat rfl
  obtain ⟨l0, m0, s0, read0, p0, c0, a0, w0, store0⟩ := store entered enteredCall
    (MemoryBelow.refl _ _).accessBelow 0 (inputHalf original left 0)
  obtain ⟨l1, m1, s1, read1, p1, c1, a1, w1, store1⟩ :=
    store m0 c0 a0 1 (inputHalf original left 1)
  obtain ⟨r0, m2, s2, read2, p2, c2, a2, w2, store2⟩ :=
    store m1 c1 a1 2 (inputHalf original right 0)
  obtain ⟨r1, m3, s3, read3, p3, c3, a3, w3, store3⟩ :=
    store m2 c2 a2 3 (inputHalf original right 1)
  have kept0 := preserved.trans p0
  have kept1 := kept0.trans p1
  have kept2 := kept1.trans p2
  have load0 := vector128_input_load program original entered inputs outputs left 0 call
    enteredCall leftMember preserved
  have load1 := vector128_input_load program original m0 inputs outputs left 1 call c0
    leftMember kept0
  have load2 := vector128_input_load program original m1 inputs outputs right 0 call c1
    rightMember kept1
  have load3 := vector128_input_load program original m2 inputs outputs right 1 call c2
    rightMember kept2
  have upperLeft := c0.input_half_address leftMember 1
  have upperRight := c2.input_half_address rightMember 1
  have rightRoot : (vector128SavedFrame frame slots right).locals[0]? =
      some (.root (some (.address right))) := rfl
  have earlier := fun before after i j (lower : i < j) source target sourceSlot targetSlot =>
    vector128_prior_read specs entered before after _ slots homes i j lower source target
      sourceSlot targetSlot
  have done := continuation l0 l1 r0 r1 m3 s0 s1 s2 s3
    (earlier _ _ 0 3 (by decide) _ _ s0 s3 _ _ w3 (earlier _ _ 0 2 (by decide) _ _ s0 s2 _ _ w2
      (earlier _ _ 0 1 (by decide) _ _ s0 s1 _ _ w1 read0)))
    (earlier _ _ 1 3 (by decide) _ _ s1 s3 _ _ w3
      (earlier _ _ 1 2 (by decide) _ _ s1 s2 _ _ w2 read1))
    (earlier _ _ 2 3 (by decide) _ _ s2 s3 _ _ w3 read2) read3 (kept2.trans p3) c3 a3
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (Nat.le_trans (write_extends_allocations _ _ _ _ _ w2).next
          (write_extends_allocations _ _ _ _ _ w3).next)))
  cil_contract_steps [found, code, layout, leftArg, rightArg, vector128SavedFrame,
    enteredCall.input_formed leftMember, enteredCall.input_formed rightMember,
    c1.input_formed rightMember, c2.input_formed rightMember, rightRoot,
    load0, load1, load2, load3, upperLeft, upperRight, store0, store1, store2, store3] until done
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
