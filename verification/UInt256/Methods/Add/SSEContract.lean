import UInt256.Methods.Add.SSEScalarContract
import UInt256.Methods.Add.ScalarEntryContract

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem checked_sse_add_contract : WrappingBinaryContract (· + ·) Extracted.program Extracted.entryIndex :=
  add_contract_of_scalar (fun memory left right output call =>
    checked_sse_scalar_contract memory left right output 0 call)

#print axioms checked_sse_add_contract
end UInt256Proof.Add.Safety
