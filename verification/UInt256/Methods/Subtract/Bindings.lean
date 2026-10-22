import Extracted
import CIL.MethodIdentity

-- Names for the freshly extracted scalar Subtract/SubtractUnderflow call graph. Only the entry
-- signature is pinned; helpers are bound by call shape, so renamed or inserted helpers stay verifiable.

namespace Extracted
@[cil_code] def entryIndex : Nat := 0
abbrev entryBody := method0
example : method0Signature = "System.Void Nethermind.Int256.UInt256::Subtract(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" ∨
    method0Signature = "System.Boolean Nethermind.Int256.UInt256::SubtractUnderflow(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" := by
  first
    | exact Or.inl rfl
    | exact Or.inr rfl

bind_callee subtractVector256Index subtractVector256Body := call 3 from entryBody
bind_callee subtractScalarIndex subtractScalarBody := call 3 from subtractVector256Body
bind_callee subtractWithBorrowIndex subtractWithBorrowBody := call 4 from subtractScalarBody [0]
bind_callee subtractScalarUInt64Index subtractScalarUInt64Body := call 3 from subtractScalarBody
bind_callee storeLimbsIndex storeLimbsBody := call 5 from subtractScalarBody

end Extracted
