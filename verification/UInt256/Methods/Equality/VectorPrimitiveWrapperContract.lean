import UInt256.Methods.Equality.VectorPrimitiveWrapper

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem vector_primitive_wrapper_checked {α : Type} (encode : α → CIL.Value)
    (operation : BitVec 256 → α → CIL.Value)
    (numeric : ∀ right, numericValue (encode right) = true)
    (numericResult : ∀ left right, numericValue (operation left right) = true)
    (child : ReadOnlyScalarContract encode operation Extracted.program vectorPrimitiveIndex) :
    ReadOnlyScalarContract encode operation Extracted.program vectorPrimitiveWrapperIndex := by
  intro memory left right call
  have lookup : Extracted.program[vectorPrimitiveWrapperIndex]? = some vectorPrimitiveWrapperBody := by rfl
  have fits : FrameSetupFits vectorPrimitiveWrapperBody (scalarArguments left (encode right)) := by
    conv in vectorPrimitiveWrapperBody => cbv
    simp [FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit]
  obtain ⟨frame, entered, setup⟩ := enterFrame_succeeds _ _ memory call.1.1 fits
  have checked : (scalarArguments left (encode right)).mapM (checkedValue memory) =
      .ok (scalarArguments left (encode right)) := by
    have formed := call.input_formed (reference := left) (by simp)
    simp [scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, childFinal, certificate, cells⟩ := child entered left right enteredCall
  have formed := enteredCall.input_formed (reference := left) (by simp)
  have fetched : vectorPrimitiveWrapperBody.code[vectorPrimitiveWrapperCall]? =
      some (.call vectorPrimitiveIndex 2) := by rfl
  have stepped : step vectorPrimitiveWrapperBody (.call vectorPrimitiveIndex 2) vectorPrimitiveWrapperCall
      (scalarArguments left (encode right)) frame [.scalar (encode right), .reference (.address left)] entered =
      .ok (.call vectorPrimitiveIndex (scalarArguments left (encode right)) [] entered) := by
    simp [step, scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, certificate.1⟩
    ⟨1, vector_primitive_wrapper_return _ _ (numericResult _ _) frame childFinal⟩
  let post : Memory → List Value → Prop := fun result values =>
    result = leaveFrame frame childFinal ∧ values = [.scalar (operation (inputValue entered left) right)]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    vector_primitive_wrapper_prefix entered left (encode right) frame (numeric right) enteredCall post
      ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  rw [call.input_value_after_setup setup (by simp : left ∈ [left])] at finished
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame childFinal memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((cells id (Nat.lt_of_lt_of_le bound fresh.1.next) offset).trans (before.cells id bound offset))

#print axioms vector_primitive_wrapper_checked

end UInt256Proof.Equality.Safety
