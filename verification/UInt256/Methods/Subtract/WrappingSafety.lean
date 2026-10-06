import UInt256.Methods.Subtract.DispatchSafety
import UInt256.Methods.Subtract.WrappingSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

theorem checked_wrapping_contract : WrappingBinaryContract (· - ·)
    Extracted.program Extracted.entryIndex :=
  wrapping_contract_of_reporting checked_dispatch_contract

#print axioms checked_wrapping_contract
end UInt256Proof.Subtract.Safety
