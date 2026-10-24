import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ReductionVectorPrimitive


/-- EquivalentReduction fixture for NeInt64UInt256 on x64-v3, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract true true CIL.Value.i64 (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i64 _ Extracted.profile true true Extracted.program 0 1 rfl (fun _ => rfl)
    (UInt256Proof.Equality.SignedPrimitive.checked64 Extracted.profile Extracted.program 1 2 rfl
    (EqualityFixture.LeafPrimitiveWrapper.checked64 Extracted.profile Extracted.program 2 3 rfl rfl rfl))

#print axioms EqualityFixture.correct
