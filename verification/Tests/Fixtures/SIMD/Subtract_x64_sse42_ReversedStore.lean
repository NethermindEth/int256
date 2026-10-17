import Extracted
import UInt256.Methods.Subtract.Vector128ReversedStore

namespace UInt256Proof.Fixture.SIMD.Subtract_x64_sse42_ReversedStore

/-- StoreLimbs takes its words high first; both store call sites push them in that order. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  UInt256Proof.Subtract.Profile.subtract_wrapping_contract Extracted.program 0 1 Extracted.profile rfl
    (UInt256Proof.Subtract.Profile.checked_reversed_store_impl Extracted.program 1 2 3 4 5 6 Extracted.profile
      (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Subtract_x64_sse42_ReversedStore
