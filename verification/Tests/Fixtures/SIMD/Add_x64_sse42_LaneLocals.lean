import Extracted
import UInt256.Methods.Add.SSEShapes.LaneLocals

namespace UInt256Proof.Fixture.SIMD.Add_x64_sse42_LaneLocals

/-- The four input halves are loaded right-upper first into permuted private homes. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  UInt256Proof.Add.SSEShapes.checked_shaped_add Extracted.program 0 1 2 4 Extracted.profile rfl rfl rfl rfl rfl
    (UInt256Proof.Add.SSEShapes.lanes_helper_contract Extracted.program Extracted.profile 2 3 5
      rfl rfl rfl rfl rfl rfl)
    (UInt256Proof.Add.Safety.portable_small_contract Extracted.program 4 5 Extracted.profile rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_x64_sse42_LaneLocals
