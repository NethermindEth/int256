import UInt256.Safety.Calling
import CIL.Safety.Certificate

namespace UInt256Model.Safety

open CIL.Safety

def scalarArguments (left : Reference) (right : CIL.Value) : List Value :=
  [.reference (.address left), .scalar right]

/-- A reference receiver and a scalar argument, with a mathematical result and
    preservation of every pre-existing caller allocation. -/
def ReadOnlyScalarContract {α : Type} (encode : α → CIL.Value)
    (operation : BitVec 256 → α → CIL.Value) (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (left : Reference) (right : α),
    CallingConditions program memory [left] [] →
    ∃ fuel final,
      InvocationCertificate program method (scalarArguments left (encode right))
        memory fuel final [.scalar (operation (inputValue memory left) right)] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

end UInt256Model.Safety
