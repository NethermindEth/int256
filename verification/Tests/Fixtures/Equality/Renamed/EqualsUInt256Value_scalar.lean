import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.ReferenceScalar
import UInt256.Methods.Equality.ReferenceVectorWrapper
import UInt256.Methods.Equality.ReferenceSseWrapper
import UInt256.Methods.Equality.SignedPrimitive
import UInt256.Methods.Equality.VectorPrimitiveWrapper
import UInt256.Methods.Equality.ValueScalar

/-- Renamed fixture for EqualsUInt256Value on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.Equality.ValueScalar.encode (fun left right => .i32 (if left = right then 1 else 0)) Extracted.program 0 :=
  by
  apply UInt256Proof.ValueForwarder32.checked Extracted.profile Extracted.program 0 1 true (fun left right => if left = right then 1 else 0)
  · intro left right _; split <;> simp
  · rfl
  · exact fun m l r c => by simpa using ((UInt256Proof.Equality.ReferenceOperator.checked (fun a b => decide (a = b)) Extracted.profile false Extracted.program 1 2 rfl
    (fun m l r c => by simpa using (UInt256Proof.Equality.ReferenceScalar.checked Extracted.profile Extracted.program 2 3 rfl rfl rfl rfl) m l r c))) m l r c

#print axioms EqualityFixture.correct
