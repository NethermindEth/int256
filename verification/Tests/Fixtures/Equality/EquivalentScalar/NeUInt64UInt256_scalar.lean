import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.PrimitiveOperator
import UInt256.Methods.ValueForwarder32
import CIL.SymbolicExecution
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import UInt256.Methods.Equality.Lemmas
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.AggregateLocals
import UInt256.Safety.PrivateAggregateStore
import CIL.Safety.CallComposition
import UInt256.Methods.ConstructorSafety
import UInt256.Safety.ConstructorSetup
import CIL.Safety.ConstructComposition
import UInt256.Methods.Bitwise.ReturnSetup
import UInt256.Safety.ScalarOperatorContract


namespace EqualityFixture.Leaf

open CIL.Safety UInt256Model.Safety

/-- Short-circuit limb comparison: three early exits, then the high-limb equality. -/
def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .fieldAt 0 8,
  .bne 21,
  .arg 0,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 8 8,
  .bne 21,
  .arg 0,
  .fieldAt 16 8,
  .arg 1,
  .fieldAt 16 8,
  .bne 21,
  .arg 0,
  .fieldAt 24 8,
  .arg 1,
  .fieldAt 24 8,
  .eq,
  .ret (some .unsigned8),
  .const32 0,
  .ret (some .unsigned8)] }

def limbsEqual (memory : Memory) (left right : Reference) : BitVec 32 :=
  if inputLimb memory left 0 = inputLimb memory right 0 then
    if inputLimb memory left 1 = inputLimb memory right 1 then
      if inputLimb memory left 2 = inputLimb memory right 2 then
        if inputLimb memory left 3 = inputLimb memory right 3 then 1 else 0
      else 0
    else 0
  else 0

macro "leaf_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · assumption
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

variable (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
  (found : program[index]? = some (body profile))

include found in
theorem scalar_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (limbsEqual memory left right))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hc (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := rfl
  have hl0 := hl (0 : Fin 4)
  have hl1 := hl (1 : Fin 4)
  have hl2 := hl (2 : Fin 4)
  have hl3 := hl (3 : Fin 4)
  have hr0 := hr (0 : Fin 4)
  have hr1 := hr (1 : Fin 4)
  have hr2 := hr (2 : Fin 4)
  have hr3 := hr (3 : Fin 4)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at hl0 hl1 hl2 hl3 hr0 hr1 hr2 hr3
  refine ⟨28, ?_⟩
  by_cases e0 : inputLimb memory left 0 = inputLimb memory right 0
  · by_cases e1 : inputLimb memory left 1 = inputLimb memory right 1
    · by_cases e2 : inputLimb memory left 2 = inputLimb memory right 2
      · rw [show limbsEqual memory left right = if inputLimb memory left 3 = inputLimb memory right 3 then 1 else 0 by
          simp [limbsEqual, e0, e1, e2]]
        leaf_steps 20 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0, e1, e2
        simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        split <;> rfl
      · rw [show limbsEqual memory left right = 0 by simp [limbsEqual, e0, e1, e2]]
        leaf_steps 16 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0, e1, e2
        simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rw [show limbsEqual memory left right = 0 by simp [limbsEqual, e0, e1]]
      leaf_steps 11 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0, e1
      simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rw [show limbsEqual memory left right = 0 by simp [limbsEqual, e0]]
    leaf_steps 6 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0
    simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms scalar_run

theorem limbs_equal_value (memory : Memory) (left right : Reference) :
    limbsEqual memory left right = if inputValue memory left = inputValue memory right then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  clear leftValue rightValue
  simp only [UInt256Proof.Equality.value_eq_iff, limbsEqual]
  by_cases e0 : inputLimb memory left 0 = inputLimb memory right 0 <;>
    by_cases e1 : inputLimb memory left 1 = inputLimb memory right 1 <;>
    by_cases e2 : inputLimb memory left 2 = inputLimb memory right 2 <;>
    simp [e0, e1, e2]

include found in
theorem scalar_run_value (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  simpa only [limbs_equal_value] using scalar_run profile program index found memory left right frame call

theorem scalar_frame_fits (left right : Reference) :
    FrameSetupFits (body profile) (readOnlyArguments [left, right]) := by
  simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit]

include found in
theorem scalar_checked (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile)
    (fun left right => .i32 (if left = right then 1 else 0))
    found (scalar_frame_fits profile) (scalar_run_value profile program index found) memory left right call

#print axioms limbs_equal_value
#print axioms scalar_checked

end EqualityFixture.Leaf



namespace EqualityFixture.LeafPrimitive
open UInt256Proof UInt256Proof.Equality

open CIL.Safety UInt256Model.Safety

variable (program : CIL.Program) (primitiveIndex primitiveConstructorCall scalarIndex : Nat)
  (primitiveBody : CIL.Method) (profile : CIL.FeatureProfile)
  (lookup : program[primitiveIndex]? = some primitiveBody)
  (storeFetched : primitiveBody.code[primitiveConstructorCall + 1]? = some (.setLocal 0))
  (addrFetched : primitiveBody.code[primitiveConstructorCall + 2]? = some (.localAddr 0))
  (callFetched : primitiveBody.code[primitiveConstructorCall + 3]? = some (.call scalarIndex 2))
  (retFetched : primitiveBody.code[primitiveConstructorCall + 4]? = some (.ret (some .unsigned8)))
  (returns : primitiveBody.returnsValue = true)
  (scalarFound : program[scalarIndex]? = some (EqualityFixture.Leaf.body profile))

def primitiveArguments (left : Reference) (right : CIL.Value) : List Value :=
  [.reference (.address left), .scalar right]
include lookup storeFetched addrFetched in
theorem primitive_store_prefix (memory updated : Memory) (left home : Reference)
    (right : CIL.Value) (bits : BitVec 256) (frame : Frame)
    (slots : frame.locals = [.bytes (.aggregate 32) home])
    (stored : storeLocal memory (.bytes (.aggregate 32) home) (.scalar (.aggregate (numberBytes bits.toNat 32))) =
      .ok (.bytes (.aggregate 32) home, updated))
    (formed : form updated home = .ok home)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run program fuel primitiveIndex (primitiveConstructorCall + 3) (primitiveArguments left right) frame
        [.reference (.address home), .reference (.address left)] updated = .ok (final, values) ∧
      post final values) :
    ∃ fuel final values,
      run program fuel primitiveIndex (primitiveConstructorCall + 1)
        (primitiveArguments left right) frame [.scalar (.aggregate (numberBytes bits.toNat 32)), .reference (.address left)] memory =
        .ok (final, values) ∧ post final values := by
  rcases frame with ⟨activation, localSlots, owned, homes⟩
  change localSlots = _ at slots
  subst localSlots
  apply run_next_exists post lookup storeFetched
  · simp [step, stored, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post lookup addrFetched
  · simp [step, localAddress, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation
include lookup retFetched returns in
 theorem primitive_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : Memory)
    (boolean : flag = 0 ∨ flag = 1) :
    run program 1 primitiveIndex (primitiveConstructorCall + 4) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  rcases boolean with rfl | rfl <;>
    simp [run, lookup, retFetched, step, returns, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms primitive_store_prefix
#print axioms primitive_return

end EqualityFixture.LeafPrimitive

namespace EqualityFixture.LeafPrimitive
open UInt256Proof UInt256Proof.Equality

open CIL.Safety UInt256Model.Safety

variable (program : CIL.Program) (primitiveIndex primitiveConstructorCall scalarIndex : Nat)
  (primitiveBody : CIL.Method) (profile : CIL.FeatureProfile)
  (lookup : program[primitiveIndex]? = some primitiveBody)
  (storeFetched : primitiveBody.code[primitiveConstructorCall + 1]? = some (.setLocal 0))
  (addrFetched : primitiveBody.code[primitiveConstructorCall + 2]? = some (.localAddr 0))
  (callFetched : primitiveBody.code[primitiveConstructorCall + 3]? = some (.call scalarIndex 2))
  (retFetched : primitiveBody.code[primitiveConstructorCall + 4]? = some (.ret (some .unsigned8)))
  (returns : primitiveBody.returnsValue = true)
  (scalarFound : program[scalarIndex]? = some (EqualityFixture.Leaf.body profile))


include lookup storeFetched addrFetched callFetched retFetched returns scalarFound in
theorem primitive_finish (memory : Memory) (left home : Reference) (right : CIL.Value)
    (bits : BitVec 256) (frame : Frame) (watermark : Nat)
    (slots : frame.locals = [.bytes (.aggregate 32) home])
    (call : CallingConditions program memory [left] [])
    (writable : access memory home 32 1 true = .ok ())
    (older : left.allocation < home.allocation)
    (privateHome : watermark ≤ home.allocation)
    (privateFrame : frame.OwnedAbove watermark) :
    ∃ fuel final,
      run program fuel primitiveIndex (primitiveConstructorCall + 1)
        (primitiveArguments left right) frame [.scalar (.aggregate (numberBytes bits.toNat 32)), .reference (.address left)] memory =
        .ok (final, [.scalar (.i32 (if inputValue memory left = bits then 1 else 0))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨storedMemory, stored, storedCall, homeValue, inputsSame, preserved⟩ :=
    call.store_private_aggregate home bits writable (by simpa using older)
  have leftSame := inputsSame left (by simp)
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ :=
    EqualityFixture.Leaf.scalar_checked profile program scalarIndex scalarFound storedMemory left home storedCall
  have fl := storedCall.input_formed (reference := left) (by simp)
  have fh := storedCall.input_formed (reference := home) (by simp)
  have stepped : step primitiveBody (.call scalarIndex 2) (primitiveConstructorCall + 3)
      (primitiveArguments left right) frame [.reference (.address home), .reference (.address left)] storedMemory =
      .ok (.call scalarIndex (readOnlyArguments [left, home]) [] storedMemory) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fh, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup callFetched stepped
    ⟨childFuel, childCertificate.1⟩ ⟨1, primitive_return program primitiveIndex primitiveConstructorCall primitiveBody lookup retFetched returns _ _ frame childFinal (by split <;> simp)⟩
  let flag : BitVec 32 := if inputValue storedMemory left = inputValue storedMemory home then 1 else 0
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame childFinal ∧ values = [.scalar (.i32 flag)]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    primitive_store_prefix program primitiveIndex primitiveConstructorCall primitiveBody lookup storeFetched addrFetched memory storedMemory left home right bits frame slots stored fh post
      ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have initialFlag : flag = (if inputValue memory left = bits then 1 else 0) := by
    simp only [flag, leftSame, homeValue]
  rw [initialFlag] at finished
  refine ⟨fuel, _, finished, ?_⟩
  have after := leaveFrame_preserves_memory_below frame childFinal watermark privateFrame
  have homeBound : home.allocation < storedMemory.nextIdentity := by
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ fh
    exact (storedCall.1.1.1 _ _ present).1
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((childCells id (Nat.lt_trans (Nat.lt_of_lt_of_le bound privateHome) homeBound) offset).trans
      (preserved.cells id (Nat.lt_of_lt_of_le bound privateHome) offset))

#print axioms primitive_finish

end EqualityFixture.LeafPrimitive


namespace EqualityFixture.LeafPrimitive
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

def constructorWords (right : BitVec 64) : List Value :=
  [.scalar (.i64 right), .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0)]

variable (program : CIL.Program) (primitiveIndex primitiveConstructorCall scalarIndex constructorIndex : Nat)
  (primitiveBody : CIL.Method) (profile : CIL.FeatureProfile)
  (lookup : program[primitiveIndex]? = some primitiveBody)
  (constructFetched : primitiveBody.code[primitiveConstructorCall]? = some (.newAggregate constructorIndex 4 32))
  (storeFetched : primitiveBody.code[primitiveConstructorCall + 1]? = some (.setLocal 0))
  (addrFetched : primitiveBody.code[primitiveConstructorCall + 2]? = some (.localAddr 0))
  (callFetched : primitiveBody.code[primitiveConstructorCall + 3]? = some (.call scalarIndex 2))
  (retFetched : primitiveBody.code[primitiveConstructorCall + 4]? = some (.ret (some .unsigned8)))
  (returns : primitiveBody.returnsValue = true)
  (scalarFound : program[scalarIndex]? = some (EqualityFixture.Leaf.body profile))
  (constructorFound : program[constructorIndex]? = some (body profile))

include lookup constructFetched storeFetched addrFetched callFetched retFetched returns scalarFound constructorFound in
theorem primitive_construct (memory : Memory) (left home : Reference) (argument : CIL.Value) (right : BitVec 64)
    (frame : Frame) (watermark : Nat)
    (slots : frame.locals = [.bytes (.aggregate 32) home])
    (call : CallingConditions program memory [left] [])
    (writable : access memory home 32 1 true = .ok ())
    (older : left.allocation < home.allocation)
    (privateHome : watermark ≤ home.allocation)
    (privateFrame : frame.OwnedAbove watermark) :
    ∃ fuel final,
      run program fuel primitiveIndex primitiveConstructorCall (primitiveArguments left argument) frame
        ((constructorWords right).reverse ++ [.reference (.address left)]) memory =
        .ok (final, [.scalar (.i32 (if inputValue memory left = BitVec.ofNat 256 right.toNat then 1 else 0))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  have checked : (constructorWords right).mapM (checkedValue memory) = .ok (constructorWords right) := by
    simp [constructorWords, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨temporary, updated, stepped, updatedCall, _, preserved, fresh⟩ :=
    call.new_aggregate256 (pc := primitiveConstructorCall) (callee := constructorIndex)
      (primitiveArguments left argument) (constructorWords right) [.reference (.address left)] frame memory lookup checked
  let nextFrame := { frame with owned := temporary.allocation :: frame.owned }
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
  have homeBound : home.allocation < memory.nextIdentity := (call.1.1.1 _ _ present).1
  have watermarkBound : watermark < memory.nextIdentity := Nat.lt_of_le_of_lt privateHome homeBound
  have growth := step_extends_allocations _ _ _ _ _ _ _ _ stepped
  have updatedWritable := (preserved.access home homeBound 32 1 true).trans writable
  obtain ⟨constructed, invoked, constructedCall, outside, authority, _, loaded⟩ :=
    constructor_contract profile program constructorIndex constructorFound updated [left] temporary right 0 0 0 updatedCall
  have constructedWritable := authority.access updatedWritable (Nat.lt_of_lt_of_le homeBound growth.next)
  have readOnlyCall : CallingConditions program constructed [left] [] :=
    ⟨⟨constructedCall.1.1, constructedCall.1.2.1, by simp⟩, constructedCall.2⟩
  have owned : nextFrame.OwnedAbove watermark := by
    intro id member
    change id ∈ temporary.allocation :: frame.owned at member
    rcases List.mem_cons.mp member with rfl | member
    · rw [fresh]
      exact Nat.le_of_lt watermarkBound
    · exact privateFrame id member
  obtain ⟨tailFuel, final, tail, tailCells⟩ :=
    primitive_finish program primitiveIndex primitiveConstructorCall scalarIndex primitiveBody profile lookup storeFetched addrFetched callFetched retFetched returns scalarFound constructed left home argument (BitVec.ofNat 256 right.toNat) nextFrame watermark
      slots readOnlyCall constructedWritable older privateHome owned
  have constructorInvoke : invoke program 13 constructorIndex
      (.reference (.address temporary) :: constructorWords right) updated = .ok (constructed, []) := by
    simpa only [constructorWords, arguments] using invoked
  have constructorLoad : loadLocal constructed (.bytes (.aggregate 32) temporary) =
      .ok (.scalar (.aggregate (numberBytes (BitVec.ofNat 256 right.toNat).toNat 32))) := by simpa [packed] using loaded
  obtain ⟨fuel, finished⟩ := run_construct_exists lookup constructFetched stepped
    ⟨13, constructorInvoke⟩ constructorLoad ⟨tailFuel, tail⟩
  have leftBound : left.allocation < memory.nextIdentity := Nat.lt_trans older homeBound
  have sameLeft : (fun offset => (constructed.cells left.allocation offset).bits) =
      (fun offset => (memory.cells left.allocation offset).bits) := by
    funext offset
    have distinct : left.allocation ≠ temporary.allocation := by
      rw [fresh]
      exact Nat.ne_of_lt leftBound
    rw [outside left.allocation offset (Or.inl distinct), preserved.cells left.allocation leftBound offset]
  have leftValue : inputValue constructed left = inputValue memory left := by
    simp only [inputValue, sameLeft]
  rw [leftValue] at finished
  refine ⟨fuel, final, finished, ?_⟩
  intro id bound offset
  have old : id < memory.nextIdentity := Nat.lt_trans bound watermarkBound
  have distinct : id ≠ temporary.allocation := by
    rw [fresh]
    exact Nat.ne_of_lt old
  exact (tailCells id bound offset).trans
    ((outside id offset (Or.inl distinct)).trans (preserved.cells id old offset))

#print axioms primitive_construct
end EqualityFixture.LeafPrimitive


namespace EqualityFixture.LeafPrimitive
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety

def PrimitivePrefix (program : CIL.Program) (index pc : Nat) (argument : CIL.Value) (word : BitVec 64) : Prop :=
  ∀ memory left frame, CallingConditions program memory [left] [] →
    ∀ post : Memory → List Value → Prop,
      (∃ fuel final values,
        run program fuel index pc (primitiveArguments left argument) frame
          ((constructorWords word).reverse ++ [.reference (.address left)]) memory = .ok (final, values) ∧
        post final values) →
      ∃ fuel final values,
        run program fuel index 0 (primitiveArguments left argument) frame [] memory =
          .ok (final, values) ∧ post final values

theorem primitive_setup (primitiveBody : CIL.Method)
    (kinds : primitiveBody.localKinds = [.aggregate 32])
    (initializers : primitiveBody.locals = [.aggregate (List.replicate 32 0)])
    (vectorArgs : primitiveBody.vectorArgs = []) (parameters : primitiveBody.parameterHomes = [])
    (program : CIL.Program) (memory : Memory) (left : Reference) (right : CIL.Value)
    (call : CallingConditions program memory [left] []) :
    ∃ frame entered home,
      enterFrame primitiveBody (primitiveArguments left right) memory = .ok (frame, entered) ∧
      frame.locals = [.bytes (.aggregate 32) home] ∧
      access entered home 32 1 true = .ok () ∧
      home.allocation = memory.nextIdentity ∧
      CallingConditions program entered [left] [] ∧
      inputValue entered left = inputValue memory left := by
  obtain ⟨home, entered, setup, writableCall, before, fresh⟩ :=
    Bitwise.ReturnSafety.setup primitiveBody (primitiveArguments left right)
      kinds initializers vectorArgs parameters program memory [left] call
  exact ⟨_, entered, home, setup, rfl, writableCall.1.2.2 (wordView home) (by simp), fresh,
    call.after_frame_setup setup, call.input_value_after_setup setup (by simp)⟩

variable (program : CIL.Program) (primitiveIndex primitiveConstructorCall scalarIndex constructorIndex : Nat)
  (primitiveBody : CIL.Method) (profile : CIL.FeatureProfile)
  (lookup : program[primitiveIndex]? = some primitiveBody)
  (constructFetched : primitiveBody.code[primitiveConstructorCall]? = some (.newAggregate constructorIndex 4 32))
  (storeFetched : primitiveBody.code[primitiveConstructorCall + 1]? = some (.setLocal 0))
  (addrFetched : primitiveBody.code[primitiveConstructorCall + 2]? = some (.localAddr 0))
  (callFetched : primitiveBody.code[primitiveConstructorCall + 3]? = some (.call scalarIndex 2))
  (retFetched : primitiveBody.code[primitiveConstructorCall + 4]? = some (.ret (some .unsigned8)))
  (returns : primitiveBody.returnsValue = true)
  (scalarFound : program[scalarIndex]? = some (EqualityFixture.Leaf.body profile))
  (constructorFound : program[constructorIndex]? = some (ConstructorSafety.body profile))
  (kinds : primitiveBody.localKinds = [.aggregate 32])
  (initializers : primitiveBody.locals = [.aggregate (List.replicate 32 0)])
  (vectorArgs : primitiveBody.vectorArgs = []) (parameters : primitiveBody.parameterHomes = [])

include lookup constructFetched storeFetched addrFetched callFetched retFetched returns scalarFound constructorFound kinds initializers vectorArgs parameters in
theorem primitive_checked (memory : Memory) (left : Reference) (argument : CIL.Value) (right : BitVec 64)
    (numeric : numericValue argument = true) (prefixExecution : PrimitivePrefix program primitiveIndex primitiveConstructorCall argument right)
    (call : CallingConditions program memory [left] []) :
    ∃ fuel final,
      InvocationCertificate program primitiveIndex (primitiveArguments left argument) memory fuel final
        [.scalar (.i32 (if inputValue memory left = BitVec.ofNat 256 right.toNat then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, home, setup, slots, writable, homeFresh, enteredCall, leftValue⟩ :=
    primitive_setup primitiveBody kinds initializers vectorArgs parameters program memory left argument call
  have checked : (primitiveArguments left argument).mapM (checkedValue memory) =
      .ok (primitiveArguments left argument) := by
    have formed := call.input_formed (reference := left) (by simp)
    simp [primitiveArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have formed := call.input_formed (reference := left) (by simp)
  have older : left.allocation < home.allocation := by
    rw [homeFresh]
    obtain ⟨allocation, present, _⟩ := formed_reference_live _ _ _ formed
    exact (call.1.1.1 _ _ present).1
  obtain ⟨tailFuel, final, tail, cells⟩ := primitive_construct program primitiveIndex primitiveConstructorCall scalarIndex constructorIndex primitiveBody profile lookup constructFetched storeFetched addrFetched callFetched retFetched returns scalarFound constructorFound entered left home argument right frame
    memory.nextIdentity slots enteredCall writable older (Nat.le_of_eq homeFresh.symm)
    (fun id member => (fresh.2 id member).1)
  let post : Memory → List Value → Prop := fun result values =>
    result = final ∧ values = [.scalar (.i32
      (if inputValue entered left = BitVec.ofNat 256 right.toNat then 1 else 0))]
  obtain ⟨fuel, result, values, finished, sameResult, sameValues⟩ :=
    prefixExecution entered left frame enteredCall post ⟨tailFuel, final, _, tail, rfl, rfl⟩
  subst result
  subst values
  rw [leftValue] at finished
  refine ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  intro id bound offset
  exact (cells id bound offset).trans (before.cells id bound offset)

#print axioms primitive_checked
end EqualityFixture.LeafPrimitive


namespace EqualityFixture.LeafUnsigned
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety EqualityFixture.LeafPrimitive

def body64 (profile : CIL.FeatureProfile) (scalarIndex constructorIndex : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 15,
  .arg 0,
  .arg 1,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .newAggregate constructorIndex 4 32,
  .setLocal 0,
  .localAddr 0,
  .call scalarIndex 2,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

def body32 (profile : CIL.FeatureProfile) (scalarIndex constructorIndex : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 16,
  .arg 0,
  .arg 1,
  .convU8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .newAggregate constructorIndex 4 32,
  .setLocal 0,
  .localAddr 0,
  .call scalarIndex 2,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

macro "leaf_primitive_prefix" found:term "," inactive:term : tactic => `(tactic|
  (intro memory left frame call post continuation
   have formed := call.input_formed (reference := left) (by simp)
   simp only [constructorWords, List.reverse_cons, List.reverse_nil,
     List.nil_append, List.cons_append] at continuation
   repeat' first
     | exact continuation
     | (apply run_next_exists post $found
        · simp only [body32, body64]; rfl
        · simp [body32, body64, step, primitiveArguments, checkedValue, numericValue, formValue, formed,
            pureArity, scalars, instruction, CIL.unary, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate, $inactive:term,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩))))

theorem prefix64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body64 profile scalarIndex constructorIndex)) (right : BitVec 64) :
    PrimitivePrefix program index 10 (.i64 right) right := by
  leaf_primitive_prefix found, inactive

#print axioms prefix64

theorem prefix32 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body32 profile scalarIndex constructorIndex)) (right : BitVec 32) :
    PrimitivePrefix program index 11 (.i32 right) (BitVec.zeroExtend 64 right) := by
  leaf_primitive_prefix found, inactive

#print axioms prefix32

theorem checked64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body64 profile scalarIndex constructorIndex))
    (scalarFound : program[scalarIndex]? = some (EqualityFixture.Leaf.body profile))
    (constructorFound : program[constructorIndex]? = some (ConstructorSafety.body profile)) :
    ScalarOperatorContract false false CIL.Value.i64
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  intro memory left right call
  simpa only [scalarOperatorArguments, Bool.false_eq_true, ite_false, scalarArguments, primitiveArguments,
    Bool.bne_false, decide_eq_true_eq] using
    primitive_checked program index 10 scalarIndex constructorIndex (body64 profile scalarIndex constructorIndex) profile
      found rfl rfl rfl rfl rfl rfl scalarFound constructorFound rfl rfl rfl rfl memory left (.i64 right) right
      rfl (prefix64 profile program index scalarIndex constructorIndex inactive found right) call

#print axioms checked64

set_option maxHeartbeats 800000 in
theorem checked32 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body32 profile scalarIndex constructorIndex))
    (scalarFound : program[scalarIndex]? = some (EqualityFixture.Leaf.body profile))
    (constructorFound : program[constructorIndex]? = some (ConstructorSafety.body profile)) :
    ScalarOperatorContract false false CIL.Value.i32
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  intro memory left right call
  have widen : (BitVec.zeroExtend 64 right).toNat = right.toNat :=
    BitVec.toNat_setWidth_of_le (by decide)
  simpa only [scalarOperatorArguments, Bool.false_eq_true, ite_false, scalarArguments, primitiveArguments,
    Bool.bne_false, decide_eq_true_eq, widen] using
    primitive_checked program index 11 scalarIndex constructorIndex (body32 profile scalarIndex constructorIndex) profile
      found rfl rfl rfl rfl rfl rfl scalarFound constructorFound rfl rfl rfl rfl memory left (.i32 right) (BitVec.zeroExtend 64 right)
      rfl (prefix32 profile program index scalarIndex constructorIndex inactive found right) call

#print axioms checked32
end EqualityFixture.LeafUnsigned

/-- EquivalentScalar fixture for NeUInt64UInt256 on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract true true CIL.Value.i64 (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i64 _ Extracted.profile true true Extracted.program 0 1 rfl (fun _ => rfl)
    (EqualityFixture.LeafUnsigned.checked64 Extracted.profile Extracted.program 1 2 3 rfl rfl rfl rfl)

#print axioms EqualityFixture.correct
