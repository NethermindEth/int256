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
example : method1Signature = "System.Boolean Nethermind.Int256.UInt256::SubtractImpl(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" := rfl

@[cil_code] def subtractScalarIndex : Nat := 2
abbrev subtractScalarBody := method2
example : method2Signature = "System.Boolean Nethermind.Int256.UInt256::SubtractScalar(Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026,Nethermind.Int256.UInt256\u0026)" := rfl

@[cil_code] def subtractWithBorrowIndex : Nat := 3
abbrev subtractWithBorrowBody := method3
example : method3Signature = "System.Void Nethermind.Int256.UInt256::SubtractWithBorrow(System.UInt64,System.UInt64,System.UInt64\u0026,System.UInt64\u0026)" := rfl

@[cil_code] def subtractScalarUInt64Index : Nat := 4
abbrev subtractScalarUInt64Body := method4
example : method4Signature = "System.Boolean Nethermind.Int256.UInt256::SubtractScalarUInt64(Nethermind.Int256.UInt256\u0026,System.UInt64,Nethermind.Int256.UInt256\u0026)" := rfl

@[cil_code] def storeLimbsIndex : Nat := 5
abbrev storeLimbsBody := method5
example : method5Signature = "System.Void Nethermind.Int256.UInt256::StoreLimbs(Nethermind.Int256.UInt256\u0026,System.UInt64,System.UInt64,System.UInt64,System.UInt64)" := rfl

end Extracted
