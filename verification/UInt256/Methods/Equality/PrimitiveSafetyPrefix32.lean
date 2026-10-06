import UInt256.Methods.Equality.PrimitiveSafetyPrefix

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem primitive_prefix32 (right : BitVec 32) :
    PrimitivePrefix (.i32 right) (right.zeroExtend 64) := by
  intro memory left frame call post continuation
  have formed := call.input_formed (reference := left) (by simp)
  conv in primitiveIndex => cbv
  conv at continuation in primitiveIndex => cbv
  conv at continuation in primitiveConstructorCall => cbv
  simp only [constructorWords, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at continuation
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, step, primitiveArguments, checkedValue, numericValue, formValue, formed,
           pureArity, scalars, instruction, CIL.step, CIL.truth, CIL.FeatureProfile.evaluate,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms primitive_prefix32

end UInt256Proof.Equality.Safety
