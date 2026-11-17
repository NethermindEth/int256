import Extracted
import CIL.MethodIdentity
import CIL.StructuralLabels

-- Names for the freshly extracted scalar Add/AddOverflow call graph. Only the entry signature is
-- pinned; helpers are bound by call shape, so renamed or inserted helpers stay verifiable.
namespace Extracted

@[cil_code] def entryIndex : Nat := 0
abbrev entryBody := method0
bind_callee addScalarIndex addScalarBody := call 4 from entryBody
bind_call entryScalarCall := addScalarIndex from entryBody
bind_callee addWithCarryIndex addWithCarryBody := call 4 from addScalarBody [0]
bind_callee addScalarUInt64Index addScalarUInt64Body := call 3 from addScalarBody [0]
bind_callee storeLimbsIndex storeLimbsBody := call 5 from addScalarBody

example : method0Signature = "System.Void Nethermind.Int256.UInt256::Add(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)" ∨
    method0Signature = "System.Boolean Nethermind.Int256.UInt256::AddOverflow(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)" := by
  first
    | exact Or.inl rfl
    | exact Or.inr rfl

end Extracted
