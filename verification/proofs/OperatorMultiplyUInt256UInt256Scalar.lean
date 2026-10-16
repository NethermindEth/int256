import Extracted
import UInt256.Methods.Multiply.EntryContract

namespace UInt256Proof.OperatorMultiplyUInt256UInt256
open UInt256Proof.Multiply.Entry
private def context : Context :=
  scalarContext ⟨1,2,3,4,5,6,7,8,9⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl
theorem scalar_correctness : UInt256Model.Safety.AggregateReturn.BinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.AggregateReturn.binary_checked (· * ·) Extracted.profile Extracted.program 0 1 rfl
    (scalar_initialized_result context rfl rfl rfl rfl rfl)
#print axioms scalar_correctness
end UInt256Proof.OperatorMultiplyUInt256UInt256
