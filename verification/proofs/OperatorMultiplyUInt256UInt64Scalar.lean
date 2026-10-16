import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.EntryPrimitiveSafety

namespace UInt256Proof.OperatorMultiplyUInt256UInt64
open UInt256Proof.Multiply.Entry
private def context : Context :=
  scalarContext ⟨1,2,3,4,5,6,7,8,9⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl
private def primitiveContext : PrimitiveContext := ⟨context, 0, 10, 11, false, false, rfl, rfl, rfl⟩
theorem scalar_correctness : UInt256Model.Safety.OrderedScalarContract false CIL.Value.i64 (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  primitive64_correctness primitiveContext rfl rfl rfl rfl rfl rfl

#print axioms scalar_correctness
end UInt256Proof.OperatorMultiplyUInt256UInt64
