import Extracted
import UInt256.Methods.CalleeBinding

-- Names for the freshly extracted scalar Add/AddOverflow call graph. Only the entry signature is
-- pinned; helpers are found by call arity, so renamed or inserted helpers stay verifiable.
namespace Extracted

@[cil_code] def entryIndex : Nat := 0
abbrev entryBody := method0
bind_callee addScalarIndex addScalarBody := entryBody with 4
bind_call_site entryScalarCall := entryBody with 4
bind_callee addWithCarryIndex addWithCarryBody := addScalarBody with 4
bind_callee addScalarUInt64Index addScalarUInt64Body := addScalarBody with 3
bind_callee storeLimbsIndex storeLimbsBody := addScalarBody with 5

example : method0Signature = "System.Void Nethermind.Int256.UInt256::Add(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)" ∨
    method0Signature = "System.Boolean Nethermind.Int256.UInt256::AddOverflow(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)" := by
  first
    | exact Or.inl rfl
    | exact Or.inr rfl

end Extracted
