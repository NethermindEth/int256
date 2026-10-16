import UInt256.Methods.Equality.PrimitiveConstruct
import UInt256.Methods.Bitwise.ReturnSetup

namespace UInt256Proof.Equality.PrimitiveFinish
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
  (scalarFound : program[scalarIndex]? = some (ScalarLeaf.body profile))
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
end UInt256Proof.Equality.PrimitiveFinish
