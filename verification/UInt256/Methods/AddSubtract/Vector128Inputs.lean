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

#print axioms vector128_local_store
#print axioms vector128_input_load

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

#print axioms vector128_prior_read
end UInt256Proof.AddSubtract.Safety

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

def vector128PrefixCode : List CIL.Op := [
  .arg 0,
  .memory .asRef,
  .memory .asRef,
  .arg 1,
  .memory .asRef,
  .memory .asRef,
  .setLocal 0,
  .dup,
  .memory .load128,
  .setLocal 1,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 2,
  .local 0,
  .memory .load128,
  .setLocal 3,
  .local 0,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 4]

def vector128OperandLocal (right upper : Bool) : Nat :=
  (if right then 2 else 0) + (if upper then 1 else 0)

def vector128OperandLoad (right upper : Bool) : Nat :=
  if right then (if upper then 20 else 15) else (if upper then 12 else 8)

def vector128ZeroSpec : NumericLocalSpec := ⟨.vector128, .v128 0, 0, rfl⟩

/-- Each actual half-load/private-store pair captures initial caller bytes. -/
theorem vector128_operand_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128PrefixCode ++ tail)
    (firstFour : ∀ i : Fin 4, specs[i.val]? = some vector128ZeroSpec)
    (original entered current : Memory)
    (inputs outputs : List Reference) (input : Reference) (frame : Frame)
    (root : LocalSlot) (slots : List LocalSlot) (args rest : List Value)
    (layout : frame.locals = root :: slots)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : input ∈ inputs) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (right upper : Bool)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[vector128OperandLocal right upper + 1]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok
        (numberBytes (inputHalf original input (if upper then 1 else 0)).toNat 16) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (inputHalf original input (if upper then 1 else 0)).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (vector128OperandLoad right upper + 2)
          args frame rest after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (vector128OperandLoad right upper) args frame
        (.reference (.address { input with offset := input.offset + 16 * (if upper then 1 else 0) }) :: rest)
        current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[vector128OperandLocal right upper]? = some vector128ZeroSpec := by
    exact firstFour ⟨vector128OperandLocal right upper, by cases right <;> cases upper <;> decide⟩
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs original.nextIdentity entered current inputs outputs frame root slots
      layout currentCall enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (inputHalf original input (if upper then 1 else 0)))
      (inputHalf original input (if upper then 1 else 0)).toNat rfl
  have done := continuation reference after slot loaded (preserved.trans retained) afterCall afterAuthority written
  have reading := vector128_input_load program original current inputs outputs input
    (if upper then 1 else 0) call currentCall member preserved

  cases right <;> cases upper <;>
    simp only [vector128OperandLoad, vector128OperandLocal, Bool.false_eq_true, ite_false, ite_true,
      Fin.val_zero, Fin.val_one] at stored reading done ⊢
  all_goals
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at reading
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, vector128PrefixCode]; rfl)
         first
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, staticInstruction, memoryInstruction, reading, checkedAt, Except.mapError,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_operand_checked
end UInt256Proof.AddSubtract.Safety

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

def vector128SavedFrame (frame : Frame) (slots : List LocalSlot) (right : Reference) : Frame :=
  { frame with locals := .root (some (.address right)) :: slots }

/-- Both input references pass the checked formation operations before the right reference is saved in its root and the left one is duplicated. -/
theorem vector128_reference_prefix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128PrefixCode ++ tail)
    (memory : Memory) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (initial : Option ManagedReference)
    (layout : frame.locals = .root initial :: slots) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (leftFormed : form memory left = .ok left)
    (rightFormed : form memory right = .ok right)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method 8 args (vector128SavedFrame frame slots right)
        [.reference (.address left), .reference (.address left)] memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] memory = .ok (result, returned) ∧
      post result returned := by

  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, vector128PrefixCode]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, leftArg, rightArg, checkedValue, formValue, leftFormed, rightFormed,
           staticInstruction, memoryInstruction, storeLocal, layout, vector128SavedFrame,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The extracted signed offset computes the upper half within the live input allocation and its permitted view, before any load is attempted. -/
theorem vector128_left_upper (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128PrefixCode ++ tail)
    (memory : Memory) (inputs outputs : List Reference)
    (left : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program memory inputs outputs)
    (member : left ∈ inputs) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method 12 args frame
        [.reference (.address { left with offset := left.offset + 16 })] memory =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 10 args frame [.reference (.address left)] memory =
        .ok (result, returned) ∧ post result returned := by
  have advanced := call.input_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at advanced

  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, vector128PrefixCode]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, staticInstruction, memoryInstruction, CIL.offsetValue, referenceAt, advanced,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Reload the tracked right-input root and, for the upper half, perform the checked offset instruction before the next vector load. -/
theorem vector128_right_reference (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128PrefixCode ++ tail)
    (memory : Memory) (inputs outputs : List Reference)
    (right : Reference) (frame : Frame) (args : List Value)
    (slot : frame.locals[0]? = some (.root (some (.address right))))
    (call : CallingConditions program memory inputs outputs)
    (member : right ∈ inputs) (upper : Bool) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if upper then 20 else 15) args frame
        [.reference (.address { right with offset := right.offset + 16 * (if upper then 1 else 0) })] memory =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (if upper then 17 else 14) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have formed := call.input_formed member
  have advanced := call.input_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at advanced

  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.mul_zero,
    Nat.mul_one, Nat.add_zero] at continuation ⊢
  all_goals
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by simp [code, vector128PrefixCode]; rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, slot, loadLocal, formValue, formed, staticInstruction, memoryInstruction,
             CIL.offsetValue, referenceAt, advanced, checkedAt, Except.mapError,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_reference_prefix
#print axioms vector128_left_upper
#print axioms vector128_right_reference
end UInt256Proof.AddSubtract.Safety

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Save all four initial input halves before arithmetic or caller output writes. -/
theorem vector128_inputs_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128PrefixCode ++ tail)
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
  have authority : AccessBelow entered.nextIdentity entered entered := (MemoryBelow.refl _ _).accessBelow
  let saved := vector128SavedFrame frame slots right
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have savedRoot : saved.locals[0]? = some (.root (some (.address right))) := rfl
  apply vector128_reference_prefix program body method found tail code entered left right frame slots (some .null) layout args leftArg rightArg
    (enteredCall.input_formed leftMember) (enteredCall.input_formed rightMember) post
  apply vector128_operand_checked program body method specs found tail code firstFour original entered entered inputs outputs left saved
    (.root (some (.address right))) slots args [.reference (.address left)] savedLayout
    call enteredCall leftMember enteredCall.1.1 homes preserved authority false false post
  intro l0 m0 s0 read0 p0 c0 a0 w0
  apply vector128_left_upper program body method found tail code m0 inputs outputs left saved args c0 leftMember post
  apply vector128_operand_checked program body method specs found tail code firstFour original entered m0 inputs outputs left saved
    (.root (some (.address right))) slots args [] savedLayout
    call c0 leftMember enteredCall.1.1 homes p0 a0 false true post
  intro l1 m1 s1 read1 p1 c1 a1 w1
  apply vector128_right_reference program body method found tail code m1 inputs outputs right saved args savedRoot c1 rightMember false post
  apply vector128_operand_checked program body method specs found tail code firstFour original entered m1 inputs outputs right saved
    (.root (some (.address right))) slots args [] savedLayout
    call c1 rightMember enteredCall.1.1 homes p1 a1 true false post
  intro r0 m2 s2 read2 p2 c2 a2 w2
  apply vector128_right_reference program body method found tail code m2 inputs outputs right saved args savedRoot c2 rightMember true post
  apply vector128_operand_checked program body method specs found tail code firstFour original entered m2 inputs outputs right saved
    (.root (some (.address right))) slots args [] savedLayout
    call c2 rightMember enteredCall.1.1 homes p2 a2 true true post
  intro r1 after s3 read3 p3 c3 a3 w3
  simp only [vector128OperandLocal, Bool.false_eq_true, ite_false, ite_true,
    Nat.reduceAdd, savedLayout, List.getElem?_cons_succ] at s0 s1 s2 s3
  have o01 := homes.ordered 0 1 .vector128 .vector128 l0 l1 (by decide) s0 s1
  have o02 := homes.ordered 0 2 .vector128 .vector128 l0 r0 (by decide) s0 s2
  have o03 := homes.ordered 0 3 .vector128 .vector128 l0 r1 (by decide) s0 s3
  have o12 := homes.ordered 1 2 .vector128 .vector128 l1 r0 (by decide) s1 s2
  have o13 := homes.ordered 1 3 .vector128 .vector128 l1 r1 (by decide) s1 s3
  have o23 := homes.ordered 2 3 .vector128 .vector128 r0 r1 (by decide) s2 s3
  have kept0 := write_preserves_disjoint_read w3
    (write_preserves_disjoint_read w2
      (write_preserves_disjoint_read w1 read0 (Or.inl (Nat.ne_of_lt o01)))
      (Or.inl (Nat.ne_of_lt o02))) (Or.inl (Nat.ne_of_lt o03))
  have kept1 := write_preserves_disjoint_read w3
    (write_preserves_disjoint_read w2 read1 (Or.inl (Nat.ne_of_lt o12))) (Or.inl (Nat.ne_of_lt o13))
  have kept2 := write_preserves_disjoint_read w3 read2 (Or.inl (Nat.ne_of_lt o23))
  exact continuation l0 l1 r0 r1 after s0 s1 s2 s3 kept0 kept1 kept2 read3 p3 c3 a3
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (Nat.le_trans (write_extends_allocations _ _ _ _ _ w2).next
          (write_extends_allocations _ _ _ _ _ w3).next)))

#print axioms vector128_inputs_checked
end UInt256Proof.AddSubtract.Safety

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

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

#print axioms vector128_other_read
end UInt256Proof.AddSubtract.Safety

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety
/-- The extracted reference root remains distinct from initialized numeric homes. -/
theorem vector128_frame_setup (body : CIL.Method) (specs : List NumericLocalSpec)
    (metadata : body.localKinds = .reference :: specs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: specs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered slots,
      enterFrame body args memory = .ok (frame, entered) ∧
      frame.locals = .root (some .null) :: slots ∧
      NumericHomes entered memory.nextIdentity specs slots ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity specs wf
  simp only [numericKinds, numericInitializers] at made
  let frame : Frame := ⟨memory.nextIdentity, .root (some .null) :: slots, owned, []⟩

  have setup : enterFrame body args memory = .ok (frame, entered) := by
    simp only [enterFrame, metadata.1, metadata.2,
      makeLocals, makeLocal, made, vectors, makeArgumentHomes, parameters, makeParameterHomes,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.nil_append, List.append_nil, List.map_nil]
    rfl
  exact ⟨frame, entered, slots, setup, rfl, homes,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup,
    enterFrame_preserves_wellFormed _ _ _ _ _ wf setup⟩

#print axioms vector128_frame_setup
end UInt256Proof.AddSubtract.Safety
