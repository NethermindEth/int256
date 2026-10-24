import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ReductionVectorPrimitive


/-- EquivalentReduction fixture for EqualsUInt32 on x64-v3, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i32 (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  (EqualityFixture.LeafPrimitiveWrapper.checked32 Extracted.profile Extracted.program 0 1 rfl rfl rfl)

#print axioms EqualityFixture.correct
