import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ScalarPrimitive


/-- EquivalentScalar fixture for EqualsUInt64 on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i64 (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  (EqualityFixture.LeafUnsigned.checked64 Extracted.profile Extracted.program 0 1 2 rfl rfl rfl rfl)

#print axioms EqualityFixture.correct
