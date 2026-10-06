import UInt256.Methods.Multiply.EntrySafetyContract
import UInt256.Safety.BinaryForwarder

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def instanceBody : CIL.Method := Extracted.program[Extracted.entryIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem multiply_instance_contract (word : WordContract) (top : FullTopContract) :
    WrappingBinaryContract (fun left right => left * right) Extracted.program Extracted.entryIndex :=
  forward_wrapping_binary Extracted.program Extracted.entryIndex multiplyIndex instanceBody _
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (multiply_checked_contract word top)

#print axioms multiply_instance_contract
end UInt256Proof.Multiply.Safety
