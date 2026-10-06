import UInt256.Methods.Multiply.ReturnSafety
import UInt256.Methods.Multiply.FullSafetyScalarTop
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open UInt256Model.Safety

theorem checked_return_contract :
    ReadOnlyContract (fun values => .v256 ((values[0]?.getD 0) * (values[1]?.getD 0)))
      Extracted.program Extracted.entryIndex 2 :=
  multiply_return_contract software_word_invoke full_scalar_top

#print axioms checked_return_contract
end UInt256Proof.Multiply.Safety
