import UInt256.Safety.ReadOnlyScalarContract

namespace UInt256Model.Safety

open CIL.Safety

def scalarOperatorArguments (scalarFirst : Bool) (left : Reference) (right : CIL.Value) : List Value :=
  if scalarFirst then [.scalar right, .reference (.address left)] else scalarArguments left right

/-- Declared operand order and polarity are part of the public contract.
    The predicate describes the initial mathematical operands. -/
def ScalarOperatorContract {α : Type} (scalarFirst negate : Bool) (encode : α → CIL.Value)
    (equal : BitVec 256 → α → Bool) (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (left : Reference) (right : α),
    CallingConditions program memory [left] [] →
    ∃ fuel final,
      InvocationCertificate program method (scalarOperatorArguments scalarFirst left (encode right)) memory fuel final
        [.scalar (.i32 (if equal (inputValue memory left) right != negate then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

end UInt256Model.Safety
