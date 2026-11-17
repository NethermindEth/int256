import UInt256.Safety.ScalarOperatorContract

namespace UInt256Model.Safety
open CIL.Safety

/-- A reference and scalar in the declared argument order, with a mathematical
    result and preservation of every pre-existing caller allocation. -/
def OrderedScalarContract {α : Type} (scalarFirst : Bool) (encode : α → CIL.Value)
    (operation : BitVec 256 → α → CIL.Value) (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (input : Reference) (scalar : α),
    CallingConditions program memory [input] [] →
    ∃ fuel final,
      InvocationCertificate program method (scalarOperatorArguments scalarFirst input (encode scalar))
        memory fuel final [.scalar (operation (inputValue memory input) scalar)] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

end UInt256Model.Safety
