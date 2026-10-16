import Extracted
import UInt256.Methods.Subtract.AcceleratedContract

namespace UInt256Proof.Subtract
open Profile

/-- SSE4.2 SubtractUnderflow: exact underflow flag and wrapping difference through the same certified call graph. -/
theorem sse_underflow_profile_correctness :
    UInt256Model.Safety.ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) Extracted.program 0 :=
  checked_accelerated_underflow_contract Extracted.program 0 1 2 3 4 5 6 Extracted.profile rfl (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl
#print axioms sse_underflow_profile_correctness
end UInt256Proof.Subtract