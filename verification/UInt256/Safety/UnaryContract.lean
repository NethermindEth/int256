import UInt256.Safety.Contract

namespace UInt256Model.Safety
open CIL.Safety

def unaryArguments (input output : Reference) : List Value :=
  [.reference (.address input), .reference (.address output)]

/-- Initialized input and writable output may overlap, including partial overlap. -/
def WrappingUnaryContract (operation : BitVec 256 → BitVec 256)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (input output : Reference),
    CallingConditions program memory [input] [output] →
    ∃ fuel final,
      InvocationCertificate program method (unaryArguments input output) memory fuel final [] ∧
      inputValue final output = operation (inputValue memory input) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

end UInt256Model.Safety
