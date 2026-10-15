import Extracted

-- Names for the freshly extracted scalar Add/AddOverflow call graph. Signature checks keep
-- the consumer bindings tied to the selected methods rather than index guesses.
namespace Extracted

@[cil_code] def entryIndex : Nat := 0
@[cil_code] def addScalarIndex : Nat := 1
@[cil_code] def addWithCarryIndex : Nat := 2
@[cil_code] def addScalarUInt64Index : Nat := 3
@[cil_code] def storeLimbsIndex : Nat := 4

abbrev entryBody := method0
abbrev addScalarBody := method1
abbrev addWithCarryBody := method2
abbrev addScalarUInt64Body := method3

example : method0Signature = "System.Void Nethermind.Int256.UInt256::Add(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)" ∨
    method0Signature = "System.Boolean Nethermind.Int256.UInt256::AddOverflow(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)" := by
  first
    | exact Or.inl rfl
    | exact Or.inr rfl
example : method1Signature = "System.Boolean Nethermind.Int256.UInt256::AddScalar(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,System.Boolean)" := rfl
example : method2Signature = "System.Void Nethermind.Int256.UInt256::AddWithCarry(System.UInt64,System.UInt64,System.UInt64&,System.UInt64&)" := rfl
example : method3Signature = "System.Boolean Nethermind.Int256.UInt256::AddScalarUInt64(Nethermind.Int256.UInt256&,System.UInt64,Nethermind.Int256.UInt256&)" := rfl
example : method4Signature = "System.Void Nethermind.Int256.UInt256::StoreLimbs(Nethermind.Int256.UInt256&,System.UInt64,System.UInt64,System.UInt64,System.UInt64)" := rfl

end Extracted
