import UInt256.Methods.Compare.PrimitiveSafetyWrapper
import UInt256.Methods.Compare.PrimitiveWrapper32

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

def wrapperSigned32 : Bool := Extracted.entryBody.code.any fun op =>
  match op with | .convI8 => true | _ => false

def widen32 (word : BitVec 32) : BitVec 64 :=
  if wrapperSigned32 then word.signExtend 64 else word.zeroExtend 64

theorem checked32 : ScalarOperatorContract wrapperScalarFirst wrapperNegate CIL.Value.i32
    (fun input word => predicate leafSigned leafScalarFirst input (widen32 word))
    Extracted.program Extracted.entryIndex :=
  PrimitiveWrapper.checked32 wrapperSigned32 leafSigned leafScalarFirst wrapperReversed wrapperNegate
    Extracted.program Extracted.entryIndex leafIndex (by rfl) (by rfl)

#print axioms checked32
end UInt256Proof.Compare.PrimitiveSafety
