import UInt256.Methods.Subtract.VectorSafetyContract
import UInt256.Methods.Subtract.WrappingSafetyCommon

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The public wrapping API inherits checked vector execution while discarding
    only its separately proved underflow flag. -/
theorem checked_vector_wrapping_contract : WrappingBinaryContract (· - ·)
    Extracted.program Extracted.entryIndex := by
  apply wrapping_contract_of_reporting
  exact checked_vector_contract

#print axioms checked_vector_wrapping_contract
end UInt256Proof.Subtract.Safety
