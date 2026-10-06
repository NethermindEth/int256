import UInt256.Methods.Multiply.ScalarSafetyOutput

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem scalar_zero (original entered current : Memory) (input output : Reference)
    (frame : Frame) (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame known) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 6 (scalarArgs input 0 output) frame [] current =
        .ok (final, returned) ∧ ScalarResult original final input output 0 returned := by
  let post := fun final returned => ScalarResult original final input output 0 returned
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have formed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 9
    apply run_next_exists post found (by rfl)
    simp [step, scalarArgs, checkedValue, numericValue, formValue, formed, checkedAt,
      pureArity, scalars, CIL.step, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract current [input] output 0 0 0 0 state.call
  have stepped : step scalarBody (.call productStoreIndex 5) 15 (scalarArgs input 0 output) frame
      [.scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0),
        .reference (.address output)] current =
      .ok (.call productStoreIndex [.reference (.address output), .scalar (.i64 0),
        .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0)] [] current) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run Extracted.program 1 scalarIndex 16 (scalarArgs input 0 output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : scalarBody.code[16]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  refine ⟨fuel, leaveFrame frame result, [], ran,
    scalar_result_of_storage original current result input output 0 frame originalCall valid owned
      state.caller ?_ readable outside⟩
  simpa using value

theorem scalar_one (original entered current : Memory) (input output : Reference)
    (frame : Frame) (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame known) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 17 (scalarArgs input 1 output) frame [] current =
        .ok (final, returned) ∧ ScalarResult original final input output 1 returned := by
  let bits := inputValue current input
  have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨result, written, valid, outside, readback⟩ := state.call.write_output_slice
    (by simp : output ∈ [output]) 0 (numberBytes bits.toNat 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  have loaded := state.call.input_load (by simp : input ∈ [input])
  have inputFormed := state.call.input_formed (by simp : input ∈ [input])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  let post := fun final returned => ScalarResult original final input output 1 returned
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 4
    apply run_next_exists post found (by rfl)
    simp [step, scalarArgs, checkedValue, formValue, inputFormed, outputFormed, checkedAt,
      staticInstruction, memoryInstruction, loaded, storeValue, referenceAt, written, bits,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  have finished : run Extracted.program 1 scalarIndex 21 (scalarArgs input 1 output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : scalarBody.code[21]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  refine ⟨1, leaveFrame frame result, [], finished,
    scalar_result_of_storage original current result input output 1 frame originalCall valid owned
      state.caller ?_ ⟨_, readback⟩ outside⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (originalCall.input_formed (by simp : input ∈ [input]))
  have bound := (originalCall.1.1.1 _ _ present).1
  have same : inputValue current input = inputValue original input := by
    unfold inputValue
    congr 1
    funext offset
    rw [state.caller input.allocation bound offset]
  simpa using
    (inputValue_of_encoded_read readback).trans same

#print axioms scalar_zero
#print axioms scalar_one
end UInt256Proof.Multiply.Safety
