import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ReductionVectorPrimitive


/-- EquivalentReduction fixture for EqUInt256UInt32 on x64-vector256, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i32 (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i32 _ Extracted.profile false false Extracted.program 0 1 rfl (fun _ => rfl)
    (EqualityFixture.LeafPrimitiveWrapper.checked32 Extracted.profile Extracted.program 1 2 rfl rfl rfl)

#print axioms EqualityFixture.correct
