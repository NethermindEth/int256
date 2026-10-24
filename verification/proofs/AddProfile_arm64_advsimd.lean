import Extracted
import UInt256.Methods.Add.ARMContract

namespace UInt256Proof.Add
open Safety

/-- AdvSimd Add: wrapping sum of the initial operands, checked finite return, writable output, caller bytes kept. -/
theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  checked_arm_add_contract Extracted.program 0 1 2 3 4 Extracted.profile rfl rfl rfl rfl rfl rfl rfl
#print axioms profile_correctness
end UInt256Proof.Add
