import UInt256.Methods.Multiply.InstanceSafety
import UInt256.Methods.Multiply.FullSafetyScalarTop
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open UInt256Model.Safety

theorem checked_instance_contract :
    WrappingBinaryContract (fun left right => left * right) Extracted.program Extracted.entryIndex :=
  multiply_instance_contract software_word_invoke full_scalar_top

#print axioms checked_instance_contract
end UInt256Proof.Multiply.Safety
