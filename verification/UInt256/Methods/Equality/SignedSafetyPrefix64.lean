import UInt256.Methods.Equality.SignedSafetyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem signed_negative64 (right : BitVec 64) (negative : right.toInt < 0) :
    SignedNegative (.i64 right) := by
  intro memory left frame call
  conv in signedIndex => cbv
  refine ⟨16, ?_⟩
  simp [run, cil_code, step, scalarArguments, checkedValue, numericValue,
    pureArity, scalars, instruction, CIL.step, negative, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem signed_positive64 (right : BitVec 64) (nonnegative : ¬right.toInt < 0) :
    SignedPositive (.i64 right) := by
  intro memory left frame call post continuation
  have formed := call.input_formed (reference := left) (by simp)
  conv in signedIndex => cbv
  conv at continuation in signedIndex => cbv
  conv at continuation in signedCall => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, step, scalarArguments, checkedValue, numericValue, formValue, formed,
           pureArity, scalars, instruction, CIL.step, nonnegative,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms signed_negative64
#print axioms signed_positive64

end UInt256Proof.Equality.Safety
