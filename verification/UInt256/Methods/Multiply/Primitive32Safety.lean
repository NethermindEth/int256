import UInt256.Methods.Multiply.PrimitiveSafetyContract
import UInt256.Methods.Multiply.WordConversion32Safety
import UInt256.Safety.OrderedScalarContract

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_primitive32_contract (word : WordContract) (top : FullTopContract) :
    OrderedScalarContract primitiveScalarFirst CIL.Value.i32
      (fun input scalar => .v256 (input * BitVec.ofNat 256 scalar.toNat))
      Extracted.program Extracted.entryIndex := by
  intro memory input scalar call
  simpa only [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using
    primitive_checked word top primitiveScalarFirst memory input (.i32 scalar) (scalar.setWidth 64)
      rfl (conversion_prefix32 scalar) (by rfl) (by rfl) (by rfl) call

#print axioms multiply_primitive32_contract
end UInt256Proof.Multiply.Safety
