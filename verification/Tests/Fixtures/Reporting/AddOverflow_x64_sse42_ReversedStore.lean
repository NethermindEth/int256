import Extracted
import UInt256.Methods.Add.SSEShapes.ReversedStore

namespace UInt256Proof.Fixture.Reporting.AddOverflow_x64_sse42_ReversedStore

/-- StoreLimbs takes its words from the top limb down; both callers push them in that order. -/
theorem correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) Extracted.program 0 :=
  UInt256Proof.Add.SSEShapes.checked_shaped_add_overflow Extracted.program 0 1 2 4 Extracted.profile rfl rfl rfl rfl rfl
    (UInt256Proof.Add.SSEShapes.reversed_store_helper_contract Extracted.program Extracted.profile 2 3 5
      rfl rfl rfl rfl rfl rfl)
    (UInt256Proof.Add.SSEShapes.reversed_small_contract Extracted.program Extracted.profile 4 5 rfl rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.Reporting.AddOverflow_x64_sse42_ReversedStore
