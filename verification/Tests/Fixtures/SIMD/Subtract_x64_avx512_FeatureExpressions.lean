import Extracted
import UInt256.Methods.Subtract.Vector256Guarded

namespace UInt256Proof.Fixture.SIMD.Subtract_x64_avx512_FeatureExpressions

/-- Each feature test is conjoined with an implied feature; the body shifts but keeps its steps. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  UInt256Proof.Subtract.Vector256.Guarded.subtract_contract Extracted.program Extracted.profile true false
    rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Subtract_x64_avx512_FeatureExpressions
