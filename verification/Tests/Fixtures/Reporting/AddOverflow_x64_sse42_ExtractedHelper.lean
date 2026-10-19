import Extracted
import UInt256.Methods.Add.SSEShapes.ExtractedHelper

namespace UInt256Proof.Fixture.Reporting.AddOverflow_x64_sse42_ExtractedHelper

/-- The lane-mask merge moves into a private helper at index 4; later callees shift by one. -/
theorem correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) Extracted.program 0 :=
  UInt256Proof.Add.SSEShapes.checked_shaped_add_overflow Extracted.program 0 1 2 5 Extracted.profile rfl rfl rfl rfl rfl
    (UInt256Proof.Add.SSEShapes.extracted_helper_contract Extracted.program Extracted.profile 2 3 4 6
      rfl rfl rfl rfl rfl rfl rfl)
    (UInt256Proof.Add.Safety.portable_small_contract Extracted.program 5 6 Extracted.profile rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.Reporting.AddOverflow_x64_sse42_ExtractedHelper
