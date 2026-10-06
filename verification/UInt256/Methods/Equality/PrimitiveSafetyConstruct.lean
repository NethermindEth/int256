import UInt256.Methods.Equality.PrimitiveSafetyFinish

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

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
