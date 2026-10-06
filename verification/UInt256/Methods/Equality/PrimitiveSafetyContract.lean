import UInt256.Methods.Equality.PrimitiveSafetyConstruct
import UInt256.Methods.Equality.PrimitiveSafetySetup

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

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
