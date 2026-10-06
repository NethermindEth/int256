import UInt256.Methods.Multiply.ScalarSafetyUnits

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
