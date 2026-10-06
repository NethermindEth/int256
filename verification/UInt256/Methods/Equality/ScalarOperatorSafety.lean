import Extracted
import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.ReadOnlyScalarExecution
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def operatorScalarFirst : Bool := match (Extracted.entryBody.code[0]? : Option CIL.Op) with
  | some (CIL.Op.arg 1) => true
  | _ => false
def operatorNegate : Bool := Extracted.entryBody.code.any fun (op : CIL.Op) => match op with
  | CIL.Op.eq => true
  | _ => false
def operatorCall : Nat := Extracted.entryBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false
def operatorCallee : Nat := match Extracted.entryBody.code[operatorCall]? with
  | some (.call callee _) => callee
  | _ => Extracted.program.length

theorem scalar_operator_prefix (memory : Memory) (left : Reference) (argument : CIL.Value)
    (frame : Frame) (numeric : numericValue argument = true)
    (call : CallingConditions Extracted.program memory [left] []) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex operatorCall
        (scalarOperatorArguments operatorScalarFirst left argument) frame
        [.scalar argument, .reference (.address left)] memory = .ok (final, values) ∧ post final values) :
    ∃ fuel final values, run Extracted.program fuel Extracted.entryIndex 0
      (scalarOperatorArguments operatorScalarFirst left argument) frame [] memory =
      .ok (final, values) ∧ post final values := by
  have formed := call.input_formed (reference := left) (by simp)
  conv in operatorScalarFirst => cbv
  conv at continuation in operatorScalarFirst => cbv
  conv at continuation in operatorCall => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, step, scalarOperatorArguments, scalarArguments, checkedValue, numeric, formValue, formed,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem scalar_operator_return (args : List Value) (equal : Bool) (frame : Frame) (memory : Memory) :
    run Extracted.program 3 Extracted.entryIndex (operatorCall + 1) args frame
      [.scalar (.i32 (if equal then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if equal != operatorNegate then 1 else 0))]) := by
  conv in operatorCall => cbv
  first
    | have polarity : operatorNegate = false := by decide
      rw [polarity]
    | have polarity : operatorNegate = true := by decide
      rw [polarity]
  simp only [Nat.reduceAdd]
  cases equal <;> simp [run, cil_code, step, pureArity, scalars, CIL.step, CIL.binary, instruction,
    checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_operator_prefix
#print axioms scalar_operator_return

end UInt256Proof.Equality.Safety
