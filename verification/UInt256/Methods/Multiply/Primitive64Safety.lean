import UInt256.Methods.Multiply.PrimitiveSafetyContract
import UInt256.Methods.Multiply.WordConversion64Safety
import UInt256.Safety.OrderedScalarContract

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_primitive64_contract (word : WordContract) (top : FullTopContract) :
    OrderedScalarContract primitiveScalarFirst CIL.Value.i64
      (fun input scalar => .v256 (input * BitVec.ofNat 256 scalar.toNat))
      Extracted.program Extracted.entryIndex := by
  intro memory input scalar call
  exact primitive_checked word top primitiveScalarFirst memory input (.i64 scalar) scalar
    rfl (conversion_prefix64 scalar) (by rfl) (by rfl) (by rfl) call

#print axioms multiply_primitive64_contract
end UInt256Proof.Multiply.Safety
