import Extracted
import UInt256.Methods.Add.ARMOverflowContract

namespace UInt256Proof.Add
open Safety

/-- AdvSimd AddOverflow: exact unsigned carry and wrapping sum of the initial operands, checked return, caller bytes kept. -/
theorem overflow_profile_correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) Extracted.program 0 :=
  checked_arm_add_overflow_contract Extracted.program 0 1 2 3 4 Extracted.profile rfl rfl rfl rfl rfl rfl rfl
#print axioms overflow_profile_correctness
end UInt256Proof.Add
