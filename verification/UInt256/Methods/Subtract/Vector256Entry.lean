import UInt256.Methods.Subtract.Vector256Contract
import UInt256.Safety.ReportingForwarder

namespace UInt256Proof.Subtract.Vector256
open UInt256Model.Safety

/-- Public AVX2 `Subtract`: wrapped difference of the initial operands; the borrow flag is discarded. -/
theorem subtract_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool)
    (entryFound : program[0]? = some (subtractEntryBody profile 1))
    (implFound : program[1]? = some (subtractImplBody profile avx512 bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1) :
    WrappingBinaryContract (· - ·) program 0 :=
  forward_reporting_pop program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile avx512 bmi1 implFound lookupFound features)

/-- Public AVX2 `SubtractUnderflow`: wrapped difference and the exact initial-operand borrow. -/
theorem subtract_underflow_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool)
    (entryFound : program[0]? = some (subtractUnderflowEntryBody profile 1))
    (implFound : program[1]? = some (subtractImplBody profile avx512 bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program 0 :=
  forward_reporting_byte program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile avx512 bmi1 implFound lookupFound features)

#print axioms subtract_contract
#print axioms subtract_underflow_contract
end UInt256Proof.Subtract.Vector256
