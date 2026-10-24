import UInt256.Methods.Subtract.DispatchSafety
import UInt256.Methods.Subtract.UnderflowSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety UInt256Proof.Subtract.Profile

theorem checked_underflow_contract (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) : ReportingBinaryContract (· - ·)
    (fun a b => decide (a.toNat < b.toNat)) Extracted.program Extracted.entryIndex :=
  underflow_contract_of_reporting (checked_dispatch_contract contract)

#print axioms checked_underflow_contract
end UInt256Proof.Subtract.Safety
