import UInt256.Methods.Subtract.Vector128DispatchSafety
import UInt256.Methods.Subtract.WrappingSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

theorem checked_vector128_wrapping_contract : WrappingBinaryContract (· - ·)
    Extracted.program Extracted.entryIndex :=
  wrapping_contract_of_reporting checked_vector128_dispatch_contract

#print axioms checked_vector128_wrapping_contract
end UInt256Proof.Subtract.Safety
