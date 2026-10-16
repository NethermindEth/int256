import UInt256.Methods.Compare.PrimitiveSafetyWrapper
import UInt256.Methods.Compare.PrimitiveWrapper64

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

theorem checked64 : ScalarOperatorContract wrapperScalarFirst wrapperNegate CIL.Value.i64
    (predicate leafSigned leafScalarFirst) Extracted.program Extracted.entryIndex :=
  PrimitiveWrapper.checked64 leafSigned leafScalarFirst wrapperReversed wrapperNegate
    Extracted.program Extracted.entryIndex leafIndex (by rfl) (by rfl)

#print axioms checked64
end UInt256Proof.Compare.PrimitiveSafety
