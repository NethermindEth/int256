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
    output_result_of_storage original current result [input] output _ frame originalCall valid owned
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
    output_result_of_storage original current result [input] output _ frame originalCall valid owned
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

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem scalar_invoke (contract : WordContract) (memory : Memory) (input output : Reference)
    (word : BitVec 64) (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel scalarIndex (scalarArgs input word output) memory = .ok (final, []) ∧
      ScalarResult memory final input output word [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := scalar_frame_setup memory input output word call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  let post := fun final returned => ScalarResult memory final input output word returned
  have started : ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 0 (scalarArgs input word output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    iterate 3
      apply run_next_exists post found (by rfl)
      simp [step, scalarArgs, checkedValue, numericValue, pureArity, scalars, CIL.step,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    by_cases large : 1 < word.toNat
    · have greater : BitVec.ofNat 64 1 < word := large
      apply run_next_exists post found (by rfl)
      · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary, large,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      simp only [greater, ite_true]
      apply scalar_products contract memory entered entered input output word frame call enteredWF homes state post
      intro current currentState
      exact scalar_output memory entered current input output word frame call enteredWF homes owned currentState
    · have unit : word = 0 ∨ word = 1 := by
        have cases : word.toNat = 0 ∨ word.toNat = 1 := by omega
        rcases cases with zero | one
        · left; exact BitVec.eq_of_toNat_eq zero
        · right; exact BitVec.eq_of_toNat_eq one
      rcases unit with rfl | rfl
      all_goals
        iterate 3
          apply run_next_exists post found (by rfl)
          simp [step, scalarArgs, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      · exact scalar_zero memory entered entered input output frame _ call owned state
      · exact scalar_one memory entered entered input output frame _ call owned state
  obtain ⟨fuel, final, returned, ran, result⟩ := started
  have returns := result.returns
  subst returned
  have inputFormed := call.input_formed (by simp : input ∈ [input])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (scalarArgs input word output).mapM (checkedValue memory) = .ok (scalarArgs input word output) := by
    simp [scalarArgs, checkedValue, numericValue, formValue, inputFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

#print axioms scalar_invoke
end UInt256Proof.Multiply.Safety
