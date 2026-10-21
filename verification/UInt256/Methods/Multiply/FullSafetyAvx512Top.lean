import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.VectorInputs
import UInt256.Methods.Multiply.VectorSteps

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

theorem full_avx512_top (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (enabled : profile.avx512DQVL = true) (avx2 : profile.avx2 = true)
    (dq : profile.avx512DQ = true) (foundation : profile.avx512F = true) (vl : profile.avx512FVL = true) :
    FullTopContract profile program methodIndex wordIndex countIndex storageIndex := by
  intro original entered current left right output frame originalCall enteredWF homes state post continuation
  let a := inputLimb original left
  let b := inputLimb original right
  let leftBits := CIL.Vector.pack256 (a 0) (a 1) (a 2) (a 3)
  let rightBits := CIL.Vector.pack256 (b 0) (b 1) (b 2) (b 3)
  have profileEq : (fullBody profile wordIndex countIndex storageIndex).profile = profile := rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have formedRight := state.call.input_formed (by simp : right ∈ [left, right])
  have loadedLeft := input_vector_snapshot state originalCall left (by simp)
  have loadedRight := input_vector_snapshot state originalCall right (by simp)
  iterate 16
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, pureArity, productArgs, checkedValue, numericValue, formValue, formedLeft, formedRight,
        staticInstruction, memoryInstruction, loadedLeft, loadedRight, checkedAt, profileEq, enabled,
        CIL.FeatureProfile.evaluate, scalars, CIL.step.eq_def, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨stored, reference, slot, stepped, storedState, readback, _⟩ := state.store_vector enteredWF homes
    22 (by rfl) rightBits 34 (productArgs left right output) [.scalar (.v256 leftBits)] (body := (fullBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by change some _ = _; simp only [enabled, ↓reduceIte] <;> rfl) stepped
  apply run_next_exists post found (by change some _ = _; simp only [enabled, ↓reduceIte] <;> rfl)
    (step_load_numeric_local .vector256 (.v256 rightBits) rightBits.toNat rfl slot readback)
  apply run_next_exists post found (by change some _ = _; simp only [enabled, ↓reduceIte] <;> rfl)
  · rfl
  apply run_next_exists post found (by change some _ = _; simp only [enabled, ↓reduceIte] <;> rfl)
    (step_reverse256 _ _ _ _ _ _ _ _ _ _ (by simpa only [profileEq] using avx2))
  apply run_next_exists post found (by change some _ = _; simp only [enabled, ↓reduceIte] <;> rfl)
    (step_mul256 _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by simp only [CIL.Intrinsic.available, profileEq, enabled, dq, foundation, vl, Bool.true_and]))
  apply run_next_exists post found (by change some _ = _; simp only [enabled, ↓reduceIte] <;> rfl)
    (step_sum256 _ _ _ _ _ _ _ _ _ _)
  obtain ⟨after, storedTop, finalState⟩ := storedState.store enteredWF homes 6 (by rfl)
    (fullTop original left right) 40 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by change some _ = _; simp only [enabled, ↓reduceIte] <;> rfl) storedTop
  apply run_next_exists post found (by rfl)
  · simp [enabled, step, pureArity, scalars, CIL.step.eq_def, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation after finalState

#print axioms full_avx512_top
end UInt256Proof.Multiply.Full