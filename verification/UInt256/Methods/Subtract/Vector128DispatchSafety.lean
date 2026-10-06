import UInt256.Methods.Subtract.Vector128ScalarChecked
import UInt256.Methods.Subtract.DispatchSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

theorem checked_vector128_dispatch_contract : ReportingBinaryContract (· - ·)
    (fun left right => decide (left.toNat < right.toNat))
    Extracted.program Extracted.subtractVector256Index :=
  dispatch_contract_of_scalar vector128_scalar_checked

#print axioms checked_vector128_dispatch_contract
end UInt256Proof.Subtract.Safety
