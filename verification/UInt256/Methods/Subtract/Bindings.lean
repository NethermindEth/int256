import Extracted
import UInt256.Methods.CalleeBinding

-- Names for the freshly extracted scalar Subtract/SubtractUnderflow call graph. Only the entry
-- signature is pinned; helpers are found by call arity, so inserted helpers stay verifiable.

namespace Extracted
@[cil_code] def entryIndex : Nat := 0
abbrev entryBody := method0
example : method0Signature = "System.Void Nethermind.Int256.UInt256::Subtract(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" ∨
    method0Signature = "System.Boolean Nethermind.Int256.UInt256::SubtractUnderflow(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" := by
  first
    | exact Or.inl rfl
    | exact Or.inr rfl

bind_callee subtractVector256Index subtractVector256Body := entryBody with 3
bind_callee subtractScalarIndex subtractScalarBody := subtractVector256Body with 3
bind_callee subtractWithBorrowIndex subtractWithBorrowBody := subtractScalarBody with 4
bind_callee subtractScalarUInt64Index subtractScalarUInt64Body := subtractScalarBody with 3
bind_callee storeLimbsIndex storeLimbsBody := subtractScalarBody with 5

end Extracted
