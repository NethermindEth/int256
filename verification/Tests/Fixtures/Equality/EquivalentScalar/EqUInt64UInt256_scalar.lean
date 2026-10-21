import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ScalarPrimitive


/-- EquivalentScalar fixture for EqUInt64UInt256 on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract true false CIL.Value.i64 (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i64 _ Extracted.profile true false Extracted.program 0 1 rfl (fun _ => rfl)
    (EqualityFixture.LeafUnsigned.checked64 Extracted.profile Extracted.program 1 2 3 rfl rfl rfl rfl)

#print axioms EqualityFixture.correct
