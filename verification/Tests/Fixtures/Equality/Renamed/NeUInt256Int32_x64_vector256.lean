import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.ReferenceScalar
import UInt256.Methods.Equality.ReferenceVectorWrapper
import UInt256.Methods.Equality.ReferenceSseWrapper
import UInt256.Methods.Equality.SignedPrimitive
import UInt256.Methods.Equality.VectorPrimitiveWrapper
import UInt256.Methods.Equality.ValueScalar

/-- Renamed fixture for NeUInt256Int32 on x64-vector256, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract false true CIL.Value.i32 (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i32 _ Extracted.profile false true Extracted.program 0 1 rfl (fun _ => rfl)
    (UInt256Proof.Equality.SignedPrimitive.checked32 Extracted.profile Extracted.program 1 2 rfl
    (UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i32 _ Extracted.profile false false Extracted.program 2 3 rfl (fun _ => rfl)
    (UInt256Proof.Equality.VectorPrimitiveWrapper.checked32 Extracted.profile Extracted.program 3 4 rfl rfl rfl)))

#print axioms EqualityFixture.correct
