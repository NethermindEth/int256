import Extracted
import UInt256.Methods.Add.Vector256Guarded

namespace UInt256Proof.Fixture.SIMD.Add_x64_avx512_FeatureExpressions

/-- The entry and PrepareAdd conjoin each feature test with an implied feature; both bodies shift by two. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  UInt256Proof.Add.Vector256.Guarded.add_contract Extracted.program Extracted.profile true
    rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_x64_avx512_FeatureExpressions
