import CIL.Safety.Certificate
import UInt256.Safety.OutputAccess
import UInt256.Safety.Calling

namespace UInt256Model.Safety

open CIL.Safety

/-- Initial-input arithmetic and caller-byte preservation, together with the
    checked CIL invocation and all supported reference/storage invariants.
    Caller conditions do not assume future execution succeeds. -/
def WrappingBinaryContract (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : CIL.Safety.Memory) (left right output : Reference),
    CallingConditions program memory [left, right] [output] →
    ∃ fuel final,
      InvocationCertificate program method (binaryArguments left right output) memory fuel final [] ∧
      inputValue final output = operation (inputValue memory left) (inputValue memory right) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

end UInt256Model.Safety
