import UInt256.Methods.Equality.PrimitiveSafetyTail
import UInt256.Methods.Equality.ScalarSafetyContract
import UInt256.Safety.PrivateAggregateStore
import CIL.Safety.CallComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

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
