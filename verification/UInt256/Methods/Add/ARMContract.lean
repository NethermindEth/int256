import UInt256.Methods.Add.ARMScalarContract
import UInt256.Methods.Add.ScalarEntryContract

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Bind the ARM dispatcher to the shared public wrapping contract. -/
theorem checked_arm_add_contract (enabled : Extracted.profile.advSimd = true) :
    WrappingBinaryContract (· + ·) Extracted.program Extracted.entryIndex := by
  apply add_contract_of_scalar
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    checked_arm_scalar_contract enabled memory left right output 0 call

#print axioms checked_arm_add_contract
end UInt256Proof.Add.Safety
