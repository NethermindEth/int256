import Extracted
import UInt256.Methods.Add.Vector256Entry
import UInt256.Methods.Add.Vector256FinishHelper

namespace UInt256Proof.Fixture.SIMD.Add_x64_avx2_bmi1_ExtractedHelper

/-- FinishAdd computes the cascade sum through a private helper; PrepareAdd moves to index 4. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  UInt256Proof.Add.Vector256.add_contract_of_callees Extracted.program Extracted.profile false 1 4 rfl
    (UInt256Proof.Add.Vector256.finish_helper_contract Extracted.program 1 2 3 Extracted.profile false
      rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩)
    (UInt256Proof.Add.Vector256.prepare_contract Extracted.program 4 Extracted.profile false rfl
      ⟨rfl, rfl, rfl, rfl⟩)
    ⟨rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_x64_avx2_bmi1_ExtractedHelper
