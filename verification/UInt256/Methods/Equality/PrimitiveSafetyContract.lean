import UInt256.Methods.Equality.PrimitiveSafetyPrefix
import CIL.Safety.NumericLocalStore
import UInt256.Methods.Equality.ScalarSafetyContract
import UInt256.Safety.PrivateAggregateStore
import CIL.Safety.CallComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

def primitiveEqualityCall : Nat := primitiveBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

theorem primitive_store_prefix (memory updated : Memory) (left home : Reference)
    (right : CIL.Value) (bits : BitVec 256) (frame : Frame)
    (slots : frame.locals = [.bytes .vector256 home])
    (stored : storeLocal memory (.bytes .vector256 home) (.scalar (.v256 bits)) =
      .ok (.bytes .vector256 home, updated))
    (formed : form updated home = .ok home)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel primitiveIndex primitiveEqualityCall (primitiveArguments left right) frame
        [.reference (.address home), .reference (.address left)] updated = .ok (final, values) ∧
      post final values) :
    ∃ fuel final values,
      run Extracted.program fuel primitiveIndex (primitiveConstructorCall + 1)
        (primitiveArguments left right) frame [.scalar (.v256 bits), .reference (.address left)] memory =
        .ok (final, values) ∧ post final values := by
  rcases frame with ⟨activation, localSlots, owned, homes⟩
  change localSlots = _ at slots
  subst localSlots
  conv in primitiveIndex => cbv
  conv in primitiveConstructorCall => cbv
  conv at continuation in primitiveIndex => cbv
  conv at continuation in primitiveEqualityCall => cbv
  simp only [Nat.reduceAdd]
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [step, stored, localAddress, formValue, formed,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem primitive_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : Memory) :
    run Extracted.program 1 primitiveIndex (primitiveEqualityCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  conv in primitiveIndex => cbv
  conv in primitiveEqualityCall => cbv
  simp only [Nat.reduceAdd]
  simp [run, cil_code, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms primitive_store_prefix
#print axioms primitive_return

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

theorem primitive_finish (memory : Memory) (left home : Reference) (right : CIL.Value)
    (bits : BitVec 256) (frame : Frame) (watermark : Nat)
    (slots : frame.locals = [.bytes .vector256 home])
    (call : CallingConditions Extracted.program memory [left] [])
    (writable : access memory home 32 1 true = .ok ())
    (older : left.allocation < home.allocation)
    (privateHome : watermark ≤ home.allocation)
    (privateFrame : frame.OwnedAbove watermark) :
    ∃ fuel final,
      run Extracted.program fuel primitiveIndex (primitiveConstructorCall + 1)
        (primitiveArguments left right) frame [.scalar (.v256 bits), .reference (.address left)] memory =
        .ok (final, [.scalar (.i32 (if inputValue memory left = bits then 1 else 0))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨storedMemory, stored, storedCall, homeValue, inputsSame, preserved⟩ :=
    call.store_private_aggregate home bits writable (by simpa using older)
  have leftSame := inputsSame left (by simp)
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ :=
    scalar_checked storedMemory left home storedCall
  have fl := storedCall.input_formed (reference := left) (by simp)
  have fh := storedCall.input_formed (reference := home) (by simp)
  have lookup : Extracted.program[primitiveIndex]? = some primitiveBody := by rfl
  have fetched : primitiveBody.code[primitiveEqualityCall]? = some (.call scalarIndex 2) := by rfl
  have stepped : step primitiveBody (.call scalarIndex 2) primitiveEqualityCall
      (primitiveArguments left right) frame [.reference (.address home), .reference (.address left)] storedMemory =
      .ok (.call scalarIndex (readOnlyArguments [left, home]) [] storedMemory) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fh, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, childCertificate.1⟩ ⟨1, primitive_return _ _ frame childFinal⟩
  let flag : BitVec 32 := if inputValue storedMemory left = inputValue storedMemory home then 1 else 0
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame childFinal ∧ values = [.scalar (.i32 flag)]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    primitive_store_prefix memory storedMemory left home right bits frame slots stored fh post
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

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

theorem primitive_construct (memory : Memory) (left home : Reference) (argument : CIL.Value) (right : BitVec 64)
    (frame : Frame) (watermark : Nat)
    (slots : frame.locals = [.bytes .vector256 home])
    (call : CallingConditions Extracted.program memory [left] [])
    (writable : access memory home 32 1 true = .ok ())
    (older : left.allocation < home.allocation)
    (privateHome : watermark ≤ home.allocation)
    (privateFrame : frame.OwnedAbove watermark) :
    ∃ fuel final,
      run Extracted.program fuel primitiveIndex primitiveConstructorCall (primitiveArguments left argument) frame
        ((constructorWords right).reverse ++ [.reference (.address left)]) memory =
        .ok (final, [.scalar (.i32 (if inputValue memory left = BitVec.ofNat 256 right.toNat then 1 else 0))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  have lookup : Extracted.program[primitiveIndex]? = some primitiveBody := by rfl
  have checked : (constructorWords right).mapM (checkedValue memory) = .ok (constructorWords right) := by
    simp [constructorWords, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨temporary, updated, stepped, updatedCall, _, preserved, fresh⟩ :=
    call.new_value (pc := primitiveConstructorCall) (callee := constructorIndex)
      (primitiveArguments left argument) (constructorWords right) [.reference (.address left)] frame memory lookup checked
  let nextFrame := { frame with owned := temporary.allocation :: frame.owned }
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
  have homeBound : home.allocation < memory.nextIdentity := (call.1.1.1 _ _ present).1
  have watermarkBound : watermark < memory.nextIdentity := Nat.lt_of_le_of_lt privateHome homeBound
  have growth := step_extends_allocations _ _ _ _ _ _ _ _ stepped
  have updatedWritable := (preserved.access home homeBound 32 1 true).trans writable
  obtain ⟨constructorFuel, constructed, invoked, constructedCall, outside, authority, _, loaded⟩ :=
    constructor_contract updated [left] temporary right 0 0 0 updatedCall
  have constructedWritable := authority.access updatedWritable (Nat.lt_of_lt_of_le homeBound growth.next)
  have readOnlyCall : CallingConditions Extracted.program constructed [left] [] :=
    ⟨⟨constructedCall.1.1, constructedCall.1.2.1, by simp⟩, constructedCall.2⟩
  have owned : nextFrame.OwnedAbove watermark := by
    intro id member
    change id ∈ temporary.allocation :: frame.owned at member
    rcases List.mem_cons.mp member with rfl | member
    · rw [fresh]
      exact Nat.le_of_lt watermarkBound
    · exact privateFrame id member
  obtain ⟨tailFuel, final, tail, tailCells⟩ :=
    primitive_finish constructed left home argument (BitVec.ofNat 256 right.toNat) nextFrame watermark
      slots readOnlyCall constructedWritable older privateHome owned
  have constructorInvoke : invoke Extracted.program constructorFuel constructorIndex
      (.reference (.address temporary) :: constructorWords right) updated = .ok (constructed, []) := by
    simpa only [constructorWords] using invoked
  have constructorLoad : loadValue constructed (.address temporary) 32 =
      .ok (.v256 (BitVec.ofNat 256 right.toNat)) := by simpa using loaded
  have fetched : primitiveBody.code[primitiveConstructorCall]? =
      some (.newValue constructorIndex (constructorWords right).length) := by rfl
  obtain ⟨fuel, finished⟩ := run_construct_exists lookup fetched stepped
    ⟨constructorFuel, constructorInvoke⟩ constructorLoad ⟨tailFuel, tail⟩
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

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

theorem primitive_setup (memory : Memory) (left : Reference) (right : CIL.Value)
    (call : CallingConditions Extracted.program memory [left] []) :
    ∃ frame entered home,
      enterFrame primitiveBody (primitiveArguments left right) memory = .ok (frame, entered) ∧
      frame.locals = [.bytes .vector256 home] ∧
      access entered home 32 1 true = .ok () ∧
      home.allocation = memory.nextIdentity ∧
      CallingConditions Extracted.program entered [left] [] ∧
      inputValue entered left = inputValue memory left := by
  obtain ⟨home, allocated, entered, allocation, _, stored, _, writable, _⟩ :=
    allocate_initialized256 memory memory.nextIdentity (BitVec.ofNat 256 0) call.1.1
  let frame : Frame := {
    activation := memory.nextIdentity, locals := [.bytes .vector256 home],
    owned := [home.allocation], arguments := [] }
  have setup : enterFrame primitiveBody (primitiveArguments left right) memory = .ok (frame, entered) := by
    conv in primitiveBody => cbv
    simp [enterFrame, makeLocals, makeLocal, localWidth, allocation, stored,
      makeArgumentHomes, frame, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨frame, entered, home, setup, rfl, writable,
    (allocateHome_fresh _ _ _ _ _ allocation).2.1,
    call.after_frame_setup setup, call.input_value_after_setup setup (by simp)⟩

#print axioms primitive_setup

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

theorem primitive_checked (memory : Memory) (left : Reference) (argument : CIL.Value) (right : BitVec 64)
    (numeric : numericValue argument = true) (prefixExecution : PrimitivePrefix argument right)
    (call : CallingConditions Extracted.program memory [left] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program primitiveIndex (primitiveArguments left argument) memory fuel final
        [.scalar (.i32 (if inputValue memory left = BitVec.ofNat 256 right.toNat then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, home, setup, slots, writable, homeFresh, enteredCall, leftValue⟩ :=
    primitive_setup memory left argument call
  have lookup : Extracted.program[primitiveIndex]? = some primitiveBody := by rfl
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
  obtain ⟨tailFuel, final, tail, cells⟩ := primitive_construct entered left home argument right frame
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

end UInt256Proof.Equality.Safety
