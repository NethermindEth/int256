import Extracted
import UInt256.Safety.ReadOnlyScalarExecution
import CIL.Safety.StepComposition
import CIL.Safety.CallComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def signedIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any (fun op => match op with | .blt _ => true | _ => false) &&
  body.code.any (fun op => match op with | .call _ _ => true | _ => false)

def signedBody : CIL.Method := Extracted.program[signedIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def signedCall : Nat := signedBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

def signedCallee : Nat :=
  match signedBody.code[signedCall]? with
  | some (.call callee _) => callee
  | _ => Extracted.program.length

/-- A proved invocation of the actual called method, including memory safety.
    This obligation is discharged by the selected scalar or vector child proof. -/
def SignedChild (argument : CIL.Value) (bits : BitVec 256) : Prop :=
  ∀ memory left, CallingConditions Extracted.program memory [left] [] →
    ∃ fuel final,
      InvocationCertificate Extracted.program signedCallee (scalarArguments left argument) memory fuel final
        [.scalar (.i32 (if inputValue memory left = bits then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

def SignedNegative (argument : CIL.Value) : Prop :=
  ∀ memory left frame, CallingConditions Extracted.program memory [left] [] →
    ∃ fuel, run Extracted.program fuel signedIndex 0
      (scalarArguments left argument) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 0)])

def SignedPositive (argument : CIL.Value) : Prop :=
  ∀ memory left frame, CallingConditions Extracted.program memory [left] [] →
    ∀ post : Memory → List Value → Prop,
      (∃ fuel final values,
        run Extracted.program fuel signedIndex signedCall
          (scalarArguments left argument) frame
          [.scalar argument, .reference (.address left)] memory = .ok (final, values) ∧
        post final values) →
      ∃ fuel final values,
        run Extracted.program fuel signedIndex 0 (scalarArguments left argument) frame [] memory =
          .ok (final, values) ∧ post final values

theorem signed_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : Memory) :
    run Extracted.program 1 signedIndex (signedCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  conv in signedIndex => cbv
  conv in signedCall => cbv
  simp only [Nat.reduceAdd]
  simp [run, cil_code, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms signed_return

/-- Signed primitive widths share the same checked negative branch. -/
macro "equality_signed_negative " negative:term : tactic => `(tactic|
  (intro memory left frame call
   conv in signedIndex => cbv
   refine ⟨16, ?_⟩
   simp [run, cil_code, step, scalarArguments, checkedValue, numericValue,
     pureArity, scalars, instruction, CIL.step, ($negative),
     Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]))

/-- Follow the actual nonnegative branch up to its checked unsigned child call. -/
macro "equality_signed_positive " nonnegative:term : tactic => `(tactic|
  (intro memory left frame call post continuation
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
            pureArity, scalars, instruction, CIL.step, ($nonnegative),
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩))))

end UInt256Proof.Equality.Safety
