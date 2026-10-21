import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ReductionVector


/-- EquivalentReduction fixture for EqualsUInt256Ref on x64-vector256, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ReadOnlyContract (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0)) Extracted.program 0 2 :=
  by
  change UInt256Model.Safety.ReadOnlyContract _ Extracted.program 0 2
  apply (by simpa using UInt256Proof.Equality.ReferenceOperator.readOnly_contract (fun a b => decide (a = b)) Extracted.program 0)
  intro memory left right call
  simpa using ((EqualityFixture.LeafVectorWrapper.checked Extracted.profile Extracted.program 0 1 rfl rfl rfl)) memory left right call

#print axioms EqualityFixture.correct
