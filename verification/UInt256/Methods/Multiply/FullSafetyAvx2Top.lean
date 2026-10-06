import UInt256.Methods.Multiply.FullSafetyAvx2Cross

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem full_avx2_finish
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (vectors : AvxCrossState original current frame left right)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord (fullInputs original left right) 6 (fullTop original left right)) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 96 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 66 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have profile : fullBody.profile = Extracted.profile := by rfl
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (inputPack original left)) (inputPack original left).toNat rfl
      vectors.operands.leftSlot vectors.operands.leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (reverseInputPack original right)) (reverseInputPack original right).toNat rfl
      vectors.operands.rightSlot vectors.operands.rightRead
  have loadCross := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (avxCrossPack original left right)) (avxCrossPack original left right).toNat rfl
      vectors.crossSlot vectors.crossRead
  iterate 10
    apply run_next_exists post found (by rfl)
    first
    | exact loadLeft _ _
    | exact loadRight _ _
    | exact loadCross _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, pureArity, checkedValue, numericValue, scalars, CIL.step, profile, Extracted.profile,
          CIL.Intrinsic.available, inputPack, reverseInputPack, avxCrossPack, avxCrossWord,
          eval_reinterpret256, eval_shift_left256, eval_even_product256, eval_add256, eval_sum256,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [narrow_low_split, lowProduct]
  obtain ⟨after, stored, finalState⟩ := state.store enteredWF homes 6 (by rfl)
    (fullTop original left right) 76 (productArgs left right output) [] (body := fullBody)
  apply run_next_exists post found (by rfl) stored
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, CIL.step, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation after finalState

theorem full_avx2_top : FullTopContract := by
  intro original entered current left right output frame originalCall enteredWF homes state post continuation
  apply full_avx2_inputs original entered current left right output frame originalCall enteredWF homes state post
  intro prepared preparedState operands
  apply full_avx2_cross original entered prepared left right output frame enteredWF homes preparedState operands post
  intro cross crossState vectors
  exact full_avx2_finish original entered cross left right output frame enteredWF homes crossState vectors post continuation

#print axioms full_avx2_finish
#print axioms full_avx2_top
end UInt256Proof.Multiply.Safety
