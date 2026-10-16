import Extracted

namespace Extracted
@[cil_code] def entryIndex : Nat := 0
abbrev entryBody := method0
example : method0Signature = "System.Void Nethermind.Int256.UInt256::Subtract(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" ∨
    method0Signature = "System.Boolean Nethermind.Int256.UInt256::SubtractUnderflow(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" := by
  first
    | exact Or.inl rfl
    | exact Or.inr rfl

@[cil_code] def subtractVector256Index : Nat := 1
abbrev subtractVector256Body := method1

@[cil_code] def subtractScalarIndex : Nat := 2
abbrev subtractScalarBody := method2

@[cil_code] def subtractWithBorrowIndex : Nat := 3
abbrev subtractWithBorrowBody := method3

@[cil_code] def subtractScalarUInt64Index : Nat := 4
abbrev subtractScalarUInt64Body := method4

@[cil_code] def storeLimbsIndex : Nat := 5
abbrev storeLimbsBody := method5

end Extracted
