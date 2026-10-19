import Extracted
import UInt256.Methods.Add.SSEShapes.FeatureExpressions

namespace UInt256Proof.Fixture.SIMD.Add_x64_sse42_FeatureExpressions

/-- Every feature guard tests its intrinsic twice; the disabled branches still fall through to SSE4.2. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  UInt256Proof.Add.SSEShapes.checked_doubled_add Extracted.program 0 1 2 4 43 true
    UInt256Proof.Add.SSEShapes.featureScalarSpecs Extracted.profile _ rfl rfl rfl
    (UInt256Proof.Add.SSEShapes.feature_scalar_shaped Extracted.profile 2 4) rfl rfl
    (UInt256Proof.Add.SSEShapes.feature_helper_contract Extracted.program Extracted.profile 2 3 5
      rfl rfl rfl rfl rfl rfl)
    (UInt256Proof.Add.SSEShapes.shifted_small_contract Extracted.program Extracted.profile 4 5 rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_x64_sse42_FeatureExpressions
