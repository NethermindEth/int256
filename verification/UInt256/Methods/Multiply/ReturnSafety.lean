import UInt256.Methods.Multiply.InitializedSafety
import UInt256.Safety.BinaryReturn

namespace UInt256Proof.Multiply.Safety
open UInt256Model.Safety

theorem multiply_return_contract (word : WordContract) (top : FullTopContract) :
    ReadOnlyContract (fun values => .v256 ((values[0]?.getD 0) * (values[1]?.getD 0)))
      Extracted.program Extracted.entryIndex 2 :=
  binary_return_contract Extracted.program Extracted.entryIndex Extracted.entryBody
    (fun left right => left * right) multiplyIndex (multiply_initialized_contract word top)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

#print axioms multiply_return_contract
end UInt256Proof.Multiply.Safety
