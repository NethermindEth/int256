import UInt256.Methods.Subtract.Vector256Contract
import UInt256.Safety.ReportingForwarder

/-!
The AVX2 subtraction entries over the `SubtractImpl` body that forms its incoming borrows with a
permute and a zero blend.
-/

namespace UInt256Proof.Subtract.Vector256.Blended
open UInt256Model.Safety UInt256Proof.Subtract.Vector256
variable {identity : Nat} {assembly : String}

/-- Blended AVX2 `Subtract`: wrapped difference of the initial operands; the borrow flag is discarded. -/
theorem subtract_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (bmi1 : Bool)
    (entryFound : program[0]? = some (subtractEntryBody profile 1))
    (implFound : program[1]? = some (subtractBlendImplBody profile bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile false bmi1) :
    WrappingBinaryContract (· - ·) program 0 :=
  forward_reporting_pop program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile false bmi1 _ 0 (.inr ⟨rfl, rfl, rfl⟩) implFound lookupFound
      features)

/-- Blended AVX2 `SubtractUnderflow`: wrapped difference and the exact initial-operand borrow. -/
theorem subtract_underflow_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (bmi1 : Bool)
    (entryFound : program[0]? = some (subtractUnderflowEntryBody profile 1))
    (implFound : program[1]? = some (subtractBlendImplBody profile bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile false bmi1) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program 0 :=
  forward_reporting_byte program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile false bmi1 _ 0 (.inr ⟨rfl, rfl, rfl⟩) implFound lookupFound
      features)

end UInt256Proof.Subtract.Vector256.Blended
