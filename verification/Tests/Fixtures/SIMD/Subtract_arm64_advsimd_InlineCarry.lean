import Extracted
import UInt256.Methods.Subtract.Vector128InlineCarry

namespace UInt256Proof.Fixture.SIMD.Subtract_arm64_advsimd_InlineCarry

/-- The repair borrow chain is inlined into nine private words; SubtractWithBorrow is gone. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  UInt256Proof.Subtract.Profile.subtract_wrapping_contract Extracted.program 0 1 Extracted.profile rfl
    (UInt256Proof.Subtract.Profile.checked_inline_carry_impl Extracted.program 1 2 3 4 5 Extracted.profile
      (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Subtract_arm64_advsimd_InlineCarry
