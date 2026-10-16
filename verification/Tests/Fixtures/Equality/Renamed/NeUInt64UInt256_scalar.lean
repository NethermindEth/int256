import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.ReferenceScalar
import UInt256.Methods.Equality.ReferenceVectorWrapper
import UInt256.Methods.Equality.ReferenceSseWrapper
import UInt256.Methods.Equality.SignedPrimitive
import UInt256.Methods.Equality.VectorPrimitiveWrapper
import UInt256.Methods.Equality.ValueScalar

/-- Renamed fixture for NeUInt64UInt256 on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract true true CIL.Value.i64 (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i64 _ Extracted.profile true true Extracted.program 0 1 rfl (fun _ => rfl)
    (UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i64 _ Extracted.profile false false Extracted.program 1 2 rfl (fun _ => rfl)
    (UInt256Proof.Equality.UnsignedPrimitive.checked64 Extracted.profile Extracted.program 2 3 4 rfl rfl rfl rfl))

#print axioms EqualityFixture.correct
