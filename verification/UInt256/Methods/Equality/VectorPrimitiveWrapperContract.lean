import UInt256.Methods.Equality.VectorPrimitiveSafety
import CIL.Safety.CallComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def vectorPrimitiveWrapperIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .call callee _ => callee == vectorPrimitiveIndex | _ => false

def vectorPrimitiveWrapperBody : CIL.Method := Extracted.program[vectorPrimitiveWrapperIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def vectorPrimitiveWrapperCall : Nat := vectorPrimitiveWrapperBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

theorem vector_primitive_wrapper_prefix (memory : Memory) (left : Reference) (argument : CIL.Value)
    (frame : Frame) (numeric : numericValue argument = true)
    (call : CallingConditions Extracted.program memory [left] []) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel vectorPrimitiveWrapperIndex vectorPrimitiveWrapperCall
        (scalarArguments left argument) frame [.scalar argument, .reference (.address left)] memory =
        .ok (final, values) ∧ post final values) :
    ∃ fuel final values, run Extracted.program fuel vectorPrimitiveWrapperIndex 0
      (scalarArguments left argument) frame [] memory = .ok (final, values) ∧ post final values := by
  have formed := call.input_formed (reference := left) (by simp)
  have wordNumeric (word : BitVec 32) : numericValue (.i32 word) = true := rfl
  conv in vectorPrimitiveWrapperIndex => cbv
  conv at continuation in vectorPrimitiveWrapperIndex => cbv
  conv at continuation in vectorPrimitiveWrapperCall => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, step, scalarArguments, checkedValue, numeric, wordNumeric, formValue, formed,
           pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem vector_primitive_wrapper_return (args : List Value) (flag : CIL.Value)
    (numeric : numericValue flag = true) (frame : Frame) (memory : Memory) :
    run Extracted.program 1 vectorPrimitiveWrapperIndex (vectorPrimitiveWrapperCall + 1) args frame
      [.scalar flag] memory = .ok (leaveFrame frame memory, [.scalar flag]) := by
  conv in vectorPrimitiveWrapperIndex => cbv
  conv in vectorPrimitiveWrapperCall => cbv
  simp only [Nat.reduceAdd]
  simp [run, cil_code, step, checkedValue, numeric,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_primitive_wrapper_prefix
#print axioms vector_primitive_wrapper_return

end UInt256Proof.Equality.Safety

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
