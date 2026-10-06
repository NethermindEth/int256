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

end UInt256Proof.Equality.Safety
