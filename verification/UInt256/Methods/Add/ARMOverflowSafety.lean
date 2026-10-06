import UInt256.Methods.Add.ARMScalarContract
import UInt256.Methods.Add.OverflowEntrySafety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

theorem checked_arm_overflow_contract : ReportingBinaryContract (· + ·)
    (fun left right => decide (2^256 ≤ left.toNat + right.toNat))
    Extracted.program Extracted.entryIndex := by
  apply overflow_contract_of_child
  intro memory left right output call
  obtain ⟨fuel, final, returned, certified, result⟩ :=
    checked_arm_scalar_contract (by rfl) memory left right output 1 call
  refine ⟨fuel, final, returned, ?_, result.wellFormed, result.value, ?_, result.writable, result.footprint⟩
  · simpa only [overflowScalarArguments, vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using certified.1
  · exact result.overflow (by decide)

#print axioms checked_arm_overflow_contract
end UInt256Proof.Add.Safety
