import Extracted
import UInt256.Methods.Add.SSEContract

namespace UInt256Proof.Add
open Safety

/-- SSE4.2 Add: wrapping sum of the initial operands, checked finite return, writable output, caller bytes kept. -/
theorem sse_profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  checked_sse_add_contract Extracted.program 0 1 2 3 4 5 Extracted.profile rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
#print axioms sse_profile_correctness
end UInt256Proof.Add
