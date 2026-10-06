import Extracted
import UInt256.Safety.ReadOnlyExecution
import UInt256.Safety.ReadOnlyForwarder
import CIL.Safety.StepComposition

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

/-- Discover a candidate comparison body; its invocation contract is proved separately. -/
def wrapperLeafIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any (fun op => match op with
    | .intrinsic (.vector (.extractMSB64 256)) _ => true
    | _ => false) ||
  (body.code.any (fun op => match op with | .field _ => true | _ => false) &&
    !(body.code.any fun op => match op with | .call _ _ => true | _ => false))

inductive Wrapper where
  | less | greater | entry

def parentIndex (child : Nat) : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .call callee _ => callee == child | _ => false

def wrapperChild : Wrapper → Nat
  | .less => wrapperLeafIndex
  | .greater => parentIndex wrapperLeafIndex
  | .entry => parentIndex (parentIndex wrapperLeafIndex)

def wrapperIndex (wrapper : Wrapper) : Nat := parentIndex (wrapperChild wrapper)
def wrapperBody (wrapper : Wrapper) : CIL.Method := Extracted.program[wrapperIndex wrapper]?.getD
  { code := [], locals := [], returnsValue := false }
def wrapperCall (wrapper : Wrapper) : Nat := (wrapperBody wrapper).code.findIdx fun op =>
  match op with | .call callee 2 => callee == wrapperChild wrapper | _ => false

def middleSwaps : Bool :=
  match (wrapperBody .greater).code[wrapperCall .greater - 2]? with
  | some (.arg 1) => true
  | _ => false

def childArguments : Wrapper → Reference → Reference → List Value
  | .less, left, right => readOnlyArguments [left, right]
  | .greater, left, right => if middleSwaps then readOnlyArguments [right, left] else readOnlyArguments [left, right]
  | .entry, left, right => readOnlyArguments [right, left]

theorem wrapper_prefix (wrapper : Wrapper) (left right : Reference) (frame : Frame) (memory : Memory)
    (call : CallingConditions Extracted.program memory [left, right] [])
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel (wrapperIndex wrapper) (wrapperCall wrapper)
        (readOnlyArguments [left, right]) frame (childArguments wrapper left right).reverse memory =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values, run Extracted.program fuel (wrapperIndex wrapper) 0
      (readOnlyArguments [left, right]) frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  cases wrapper
  all_goals
    conv in (wrapperIndex _) => cbv
    conv at continuation in (wrapperIndex _) => cbv
    conv at continuation in (wrapperCall _) => cbv
    simp only [childArguments, show middleSwaps = _ from rfl, Bool.true_eq, ite_true, ite_false, readOnlyArguments, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at continuation
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

#print axioms wrapper_prefix
end UInt256Proof.Compare.Safety
