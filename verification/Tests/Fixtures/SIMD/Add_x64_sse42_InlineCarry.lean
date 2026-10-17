import Extracted
import UInt256.Methods.Add.SSEShapes.InlineCarry

namespace UInt256Proof.Fixture.SIMD.Add_x64_sse42_InlineCarry

/-- The repair computes each limb's sum and carry inline instead of calling a carry helper. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  UInt256Proof.Add.SSEShapes.checked_scalar_add Extracted.program 0 1 2 3 41 false
    UInt256Proof.Add.SSEShapes.inlineScalarSpecs Extracted.profile _ rfl rfl rfl
    (UInt256Proof.Add.SSEShapes.inline_carry_scalar_shaped Extracted.profile 2 3) rfl rfl
    (UInt256Proof.Add.SSEShapes.inline_carry_helper_contract Extracted.program Extracted.profile 2 4
      rfl rfl rfl rfl rfl)
    (UInt256Proof.Add.Safety.portable_small_contract Extracted.program 3 4 Extracted.profile rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_x64_sse42_InlineCarry
