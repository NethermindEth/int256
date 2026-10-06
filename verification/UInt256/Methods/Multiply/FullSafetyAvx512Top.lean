import UInt256.Methods.Multiply.FullSafetyVectorInputs

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem full_avx512_top : FullTopContract := by
  intro original entered current left right output frame originalCall enteredWF homes state post continuation
  let a := inputLimb original left
  let b := inputLimb original right
  let leftBits := CIL.Vector.pack256 (a 0) (a 1) (a 2) (a 3)
  let rightBits := CIL.Vector.pack256 (b 0) (b 1) (b 2) (b 3)
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have profile : fullBody.profile = Extracted.profile := by rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have formedRight := state.call.input_formed (by simp : right ∈ [left, right])
  have loadedLeft := input_vector_snapshot state originalCall left (by simp)
  have loadedRight := input_vector_snapshot state originalCall right (by simp)
  iterate 10
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, pureArity, productArgs, checkedValue, numericValue, formValue, formedLeft, formedRight,
        staticInstruction, memoryInstruction, loadedLeft, loadedRight, checkedAt, profile, Extracted.profile,
        CIL.FeatureProfile.evaluate, scalars, CIL.step, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨stored, reference, slot, stepped, storedState, readback, _⟩ := state.store_vector enteredWF homes
    22 (by rfl) rightBits 28 (productArgs left right output) [.scalar (.v256 leftBits)] (body := fullBody)
  apply run_next_exists post found (by rfl) stepped
  apply run_next_exists post found (by rfl)
    (step_load_numeric_local .vector256 (.v256 rightBits) rightBits.toNat rfl slot readback)
  iterate 4
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, pureArity, checkedValue, numericValue, scalars, CIL.step, profile, Extracted.profile,
        CIL.Intrinsic.available, leftBits, rightBits, eval_reverse256, eval_dq_product256, eval_sum256,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, storedTop, finalState⟩ := storedState.store enteredWF homes 6 (by rfl)
    (fullTop original left right) 34 (productArgs left right output) [] (body := fullBody)
  apply run_next_exists post found (by rfl) storedTop
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, CIL.step, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation after finalState

#print axioms full_avx512_top
end UInt256Proof.Multiply.Safety
