import UInt256.Methods.ConstructorSafety
import UInt256.Safety.ConstructorSetup
import CIL.Safety.ConstructComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

def primitiveIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .newValue _ _ => true | _ => false

def primitiveBody : CIL.Method := Extracted.program[primitiveIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def primitiveConstructorCall : Nat := primitiveBody.code.findIdx fun op =>
  match op with | .newValue _ _ => true | _ => false

def primitiveArguments (left : Reference) (right : CIL.Value) : List Value :=
  [.reference (.address left), .scalar right]

def constructorWords (right : BitVec 64) : List Value :=
  [.scalar (.i64 right), .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0)]

/-- The actual entry prefix must reach the constructor with the specified word.
    This is an execution obligation, discharged separately for each input width. -/
def PrimitivePrefix (argument : CIL.Value) (word : BitVec 64) : Prop :=
  ∀ memory left frame, CallingConditions Extracted.program memory [left] [] →
    ∀ post : Memory → List Value → Prop,
      (∃ fuel final values,
        run Extracted.program fuel primitiveIndex primitiveConstructorCall
          (primitiveArguments left argument) frame
          ((constructorWords word).reverse ++ [.reference (.address left)]) memory = .ok (final, values) ∧
        post final values) →
      ∃ fuel final values,
        run Extracted.program fuel primitiveIndex 0 (primitiveArguments left argument) frame [] memory =
          .ok (final, values) ∧ post final values

/-- Both primitive widths follow the extracted prefix; only the theorem's input
    representation differs. Keep the checked stepping recipe in one place. -/
macro "equality_primitive_prefix" : tactic => `(tactic|
  (intro memory left frame call post continuation
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
          try (exact ⟨rfl, rfl, rfl, rfl⟩))))

end UInt256Proof.Equality.Safety
