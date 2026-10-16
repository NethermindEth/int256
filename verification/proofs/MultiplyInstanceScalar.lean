import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Safety.BinaryForwarder

namespace UInt256Proof.MultiplyInstance
open UInt256Proof.Multiply.Entry
private def context : Context :=
  scalarContext ⟨1,2,3,4,5,6,7,8,9⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl
theorem scalar_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.forward_wrapping_binary Extracted.program 0 1 Extracted.method0 (· * ·)
    rfl rfl rfl rfl rfl rfl rfl
    (UInt256Proof.Multiply.Entry.scalar_correctness context rfl rfl rfl rfl rfl)
#print axioms scalar_correctness
end UInt256Proof.MultiplyInstance
