import Extracted
import UInt256.Methods.Add.ARMLanes.Helper

namespace UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_LaneLocals

/-- The four input halves are loaded right-upper first into permuted AdvSimd private homes. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  UInt256Proof.Add.ARMLanes.lanes_checked_arm_add_contract Extracted.program 0 1 2 3 4 Extracted.profile
    rfl rfl rfl rfl rfl rfl rfl

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_LaneLocals
