import UInt256.Methods.Subtract.DispatchSafety
import UInt256.Methods.Subtract.WrappingSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety UInt256Proof.Subtract.Profile

theorem checked_wrapping_contract (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) : WrappingBinaryContract (· - ·)
    Extracted.program Extracted.entryIndex :=
  wrapping_contract_of_reporting (checked_dispatch_contract contract)

#print axioms checked_wrapping_contract
end UInt256Proof.Subtract.Safety
