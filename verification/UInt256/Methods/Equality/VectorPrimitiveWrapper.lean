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
           pureArity, scalars, CIL.step, CIL.truth, CIL.FeatureProfile.evaluate,
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
