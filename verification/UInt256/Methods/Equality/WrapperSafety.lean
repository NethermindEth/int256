import Extracted
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

/-- Locate a candidate leaf; its contract must still be supplied by a checked
    execution proof when composing the wrappers. -/
def equalityLeafIndex : Nat := Extracted.program.findIdx fun body =>
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false) &&
  body.code.any (fun op => match op with
    | .field _ | .intrinsic (.vector (.equalsAll 256)) _ | .intrinsic (.vector (.equalsAll 128)) _ => true
    | _ => false)

def wrapperIndex (outer : Bool) : Nat :=
  let inner := Extracted.program.findIdx fun body =>
    body.code.any fun op => match op with | .call callee _ => callee == equalityLeafIndex | _ => false
  if !outer then inner else
    let parent := Extracted.program.findIdx fun body =>
      body.aggregateArgs.isEmpty &&
      body.code.any fun op => match op with | .call callee _ => callee == inner | _ => false
    if parent < Extracted.program.length then parent else inner

def wrapperBody (outer : Bool) : CIL.Method := Extracted.program[wrapperIndex outer]?.getD
  { code := [], locals := [], returnsValue := false }

def wrapperCall (outer : Bool) : Nat := (wrapperBody outer).code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

theorem wrapper_prefix (outer : Bool) (left right : Reference) (frame : Frame) (memory : Memory)
    (call : CallingConditions Extracted.program memory [left, right] [])
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel (wrapperIndex outer) (wrapperCall outer)
        (readOnlyArguments [left, right]) frame
        [.reference (.address right), .reference (.address left)] memory = .ok (final, values) ∧
      post final values) :
    ∃ fuel final values, run Extracted.program fuel (wrapperIndex outer) 0
      (readOnlyArguments [left, right]) frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  cases outer
  all_goals
    conv in (wrapperIndex _) => cbv
    conv at continuation in (wrapperIndex _) => cbv
    conv at continuation in (wrapperCall _) => cbv
    repeat' first
      | exact continuation
      | (apply run_next_exists post
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [cil_code, readOnlyArguments, step, checkedValue, numericValue, formValue,
               fl, fr, pureArity, scalars, CIL.step, CIL.truth, CIL.FeatureProfile.evaluate,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem wrapper_return (outer : Bool) (args : List Value) (flag : BitVec 32)
    (frame : Frame) (memory : Memory)
    (forwarding : (wrapperBody outer).code[wrapperCall outer + 1]? = some .ret) :
    run Extracted.program 1 (wrapperIndex outer) (wrapperCall outer + 1) args frame
      [.scalar (.i32 flag)] memory = .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have lookup : Extracted.program[wrapperIndex outer]? = some (wrapperBody outer) := by
    cases outer <;> rfl
  have returns : (wrapperBody outer).returnsValue = true := by cases outer <;> rfl
  rw [run]
  simp [lookup, forwarding, step, returns, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms wrapper_prefix
#print axioms wrapper_return

end UInt256Proof.Equality.Safety
