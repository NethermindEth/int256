import UInt256.Methods.Add.OverflowScalarSafety
import UInt256.Methods.Add.CarryContract

namespace UInt256Proof.Safety
open UInt256Model.Safety

theorem checked_overflow_contract : ReportingBinaryContract (· + ·)
    (fun left right => decide (2^256 ≤ left.toNat + right.toNat))
    Extracted.program Extracted.entryIndex :=
  overflow_contract_of_child (overflow_scalar_checked
    (UInt256Proof.Add.CarrySafety.carry_helper_contract (profile := Extracted.profile) rfl))

#print axioms checked_overflow_contract
end UInt256Proof.Safety
