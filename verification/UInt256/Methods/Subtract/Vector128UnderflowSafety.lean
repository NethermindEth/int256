import UInt256.Methods.Subtract.Vector128DispatchSafety
import UInt256.Methods.Subtract.UnderflowSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

theorem checked_vector128_underflow_contract : ReportingBinaryContract (· - ·)
    (fun a b => decide (a.toNat < b.toNat)) Extracted.program Extracted.entryIndex :=
  underflow_contract_of_reporting checked_vector128_dispatch_contract

#print axioms checked_vector128_underflow_contract
end UInt256Proof.Subtract.Safety
