import Extracted
import UInt256.Methods.Compare.PrimitiveValue

theorem UInt256Proof.Compare.LeUInt64UInt256.scalar_correctness :
    UInt256Proof.Compare.PrimitiveValue.Contract Extracted.program 0 :=
  UInt256Proof.Compare.PrimitiveValue.correctness Extracted.program 0 1 (by rfl) (by rfl)

#print axioms UInt256Proof.Compare.LeUInt64UInt256.scalar_correctness
