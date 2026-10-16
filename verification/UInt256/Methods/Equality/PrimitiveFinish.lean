import UInt256.Methods.Equality.ScalarLeaf
import CIL.Safety.AggregateLocals

import UInt256.Safety.PrivateAggregateStore
import CIL.Safety.CallComposition

namespace UInt256Proof.Equality.PrimitiveFinish

open CIL.Safety UInt256Model.Safety

variable (program : CIL.Program) (primitiveIndex primitiveConstructorCall scalarIndex : Nat)
  (primitiveBody : CIL.Method) (profile : CIL.FeatureProfile)
  (lookup : program[primitiveIndex]? = some primitiveBody)
  (storeFetched : primitiveBody.code[primitiveConstructorCall + 1]? = some (.setLocal 0))
  (addrFetched : primitiveBody.code[primitiveConstructorCall + 2]? = some (.localAddr 0))
  (callFetched : primitiveBody.code[primitiveConstructorCall + 3]? = some (.call scalarIndex 2))
  (retFetched : primitiveBody.code[primitiveConstructorCall + 4]? = some (.ret (some .unsigned8)))
  (returns : primitiveBody.returnsValue = true)
  (scalarFound : program[scalarIndex]? = some (ScalarLeaf.body profile))

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

end UInt256Proof.Equality.PrimitiveFinish

namespace UInt256Proof.Equality.PrimitiveFinish

open CIL.Safety UInt256Model.Safety

variable (program : CIL.Program) (primitiveIndex primitiveConstructorCall scalarIndex : Nat)
  (primitiveBody : CIL.Method) (profile : CIL.FeatureProfile)
  (lookup : program[primitiveIndex]? = some primitiveBody)
  (storeFetched : primitiveBody.code[primitiveConstructorCall + 1]? = some (.setLocal 0))
  (addrFetched : primitiveBody.code[primitiveConstructorCall + 2]? = some (.localAddr 0))
  (callFetched : primitiveBody.code[primitiveConstructorCall + 3]? = some (.call scalarIndex 2))
  (retFetched : primitiveBody.code[primitiveConstructorCall + 4]? = some (.ret (some .unsigned8)))
  (returns : primitiveBody.returnsValue = true)
  (scalarFound : program[scalarIndex]? = some (ScalarLeaf.body profile))


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
    ScalarLeaf.scalar_checked profile program scalarIndex scalarFound storedMemory left home storedCall
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

end UInt256Proof.Equality.PrimitiveFinish
