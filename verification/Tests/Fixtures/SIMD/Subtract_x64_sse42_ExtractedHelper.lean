import Extracted
import UInt256.Methods.Subtract.Vector128ExtractedHelpers

namespace UInt256Proof.Fixture.SIMD.Subtract_x64_sse42_ExtractedHelper

/-- The propagation merge moves into a private helper; StoreLimbs moves to index 7. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  UInt256Proof.Subtract.Profile.subtract_wrapping_contract Extracted.program 0 1 Extracted.profile rfl
    (UInt256Proof.Subtract.Profile.checked_extracted_helpers_impl Extracted.program 1 2 3 0 5 4 6 7 Extracted.profile
      (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (fun h => absurd h (by decide)) rfl rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Subtract_x64_sse42_ExtractedHelper
