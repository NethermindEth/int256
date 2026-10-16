import UInt256.Methods.Subtract.ScalarSafetyChecked
import UInt256.Methods.Subtract.DispatchSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

theorem checked_dispatch_contract : ReportingBinaryContract (· - ·)
    (fun left right => decide (left.toNat < right.toNat))
    Extracted.program Extracted.subtractVector256Index :=
  dispatch_contract_of_scalar scalar_checked

#print axioms checked_dispatch_contract
end UInt256Proof.Subtract.Safety
