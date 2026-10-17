import Extracted
import UInt256.Methods.Subtract.Vector128ExtractedHelpers

namespace UInt256Proof.Fixture.Reporting.SubtractUnderflow_arm64_advsimd_ExtractedHelper

/-- The AdvSimd window extraction and the propagation merge move into private helpers. -/
theorem correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left - right)
      (fun left right => decide (left.toNat < right.toNat)) Extracted.program 0 :=
  UInt256Proof.Subtract.Profile.subtract_underflow_contract Extracted.program 0 1 Extracted.profile rfl
    (UInt256Proof.Subtract.Profile.checked_extracted_helpers_impl Extracted.program 1 2 3 6 5 4 7 8 Extracted.profile
      (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (fun _ => rfl) rfl rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.Reporting.SubtractUnderflow_arm64_advsimd_ExtractedHelper
