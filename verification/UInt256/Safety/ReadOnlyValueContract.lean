import UInt256.Safety.Calling
import CIL.Safety.Certificate

namespace UInt256Model.Safety

open CIL.Safety

def valueArguments (left : Reference) (right : BitVec 256) : List Value :=
  [.reference (.address left), .scalar (.v256 right)]

/-- One initialized reference input and one passed value; no second caller
    allocation or disjointness assumption is required. -/
def ReadOnlyValueContract (operation : BitVec 256 → BitVec 256 → CIL.Value)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (left : Reference) (right : BitVec 256),
    CallingConditions program memory [left] [] →
    ∃ fuel final,
      InvocationCertificate program method (valueArguments left right) memory fuel final
        [.scalar (operation (inputValue memory left) right)] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

end UInt256Model.Safety
