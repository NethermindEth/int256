import Extracted
import UInt256.Methods.Subtract.AcceleratedContract

namespace UInt256Proof.Subtract
open Profile

/-- SSE4.2 Subtract: wrapping difference of the initial operands, checked finite return, writable output, caller bytes kept. -/
theorem sse_profile_correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  checked_accelerated_subtract_contract Extracted.program 0 1 2 3 4 5 6 Extracted.profile rfl (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl
#print axioms sse_profile_correctness
end UInt256Proof.Subtract