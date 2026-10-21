import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ReductionVectorPrimitive


/-- EquivalentReduction fixture for EqualsInt64 on x64-vector256, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i64 (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.SignedPrimitive.checked64 Extracted.profile Extracted.program 0 1 rfl
    (EqualityFixture.LeafPrimitiveWrapper.checked64 Extracted.profile Extracted.program 1 2 rfl rfl rfl)

#print axioms EqualityFixture.correct
