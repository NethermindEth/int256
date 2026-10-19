import Extracted
import UInt256.Methods.Subtract.Vector256Helper

namespace UInt256Proof.Fixture.SIMD.Subtract_x64_avx2_ExtractedHelper

/-- SubtractImpl computes the cascade sum through a private helper at index 3. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  UInt256Proof.Subtract.Vector256.Helper.subtract_contract Extracted.program Extracted.profile false false
    rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Subtract_x64_avx2_ExtractedHelper
