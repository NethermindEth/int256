import Extracted
import UInt256.Methods.Bindings
import Tests.Fixtures.Equality.Shared.ScalarReference


/-- EquivalentScalar fixture for EqualsUInt256Value on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.Equality.ValueScalar.encode (fun left right => .i32 (if left = right then 1 else 0)) Extracted.program 0 :=
  by
  apply UInt256Proof.ValueForwarder32.checked Extracted.profile Extracted.program 0 1 true (fun left right => if left = right then 1 else 0)
  · intro left right _; split <;> simp
  · rfl
  · exact fun m l r c => by simpa using ((EqualityFixture.LeafReference.checked Extracted.profile Extracted.program 1 2 rfl rfl rfl rfl)) m l r c

#print axioms EqualityFixture.correct
