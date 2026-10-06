import UInt256.Methods.Subtract.VectorSafetyContract
import UInt256.Methods.Subtract.UnderflowSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

theorem checked_vector_underflow_contract : ReportingBinaryContract (· - ·)
    (fun a b => decide (a.toNat < b.toNat)) Extracted.program Extracted.entryIndex := by
  apply underflow_contract_of_reporting
  exact checked_vector_contract

#print axioms checked_vector_underflow_contract
end UInt256Proof.Subtract.Safety
