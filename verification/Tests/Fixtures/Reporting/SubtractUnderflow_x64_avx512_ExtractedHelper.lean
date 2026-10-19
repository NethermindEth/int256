import Extracted
import UInt256.Methods.Subtract.Vector256Helper

namespace UInt256Proof.Fixture.Reporting.SubtractUnderflow_x64_avx512_ExtractedHelper

/-- SubtractImpl computes the cascade sum through a private helper at index 3. -/
theorem correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left - right)
      (fun left right => decide (left.toNat < right.toNat)) Extracted.program 0 :=
  UInt256Proof.Subtract.Vector256.Helper.subtract_underflow_contract Extracted.program Extracted.profile true false
    rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.Reporting.SubtractUnderflow_x64_avx512_ExtractedHelper
