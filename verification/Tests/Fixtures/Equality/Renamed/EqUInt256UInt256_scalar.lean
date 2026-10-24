import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.ReferenceScalar
import UInt256.Methods.Equality.ReferenceVectorWrapper
import UInt256.Methods.Equality.ReferenceSseWrapper
import UInt256.Methods.Equality.SignedPrimitive
import UInt256.Methods.Equality.VectorPrimitiveWrapper
import UInt256.Methods.Equality.ValueScalar

/-- Renamed fixture for EqUInt256UInt256 on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ReadOnlyContract (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0)) Extracted.program Extracted.entryIndex 2 :=
  by
  change UInt256Model.Safety.ReadOnlyContract _ Extracted.program 0 2
  apply (by simpa using UInt256Proof.Equality.ReferenceOperator.readOnly_contract (fun a b => decide (a = b)) Extracted.program 0)
  intro memory left right call
  simpa using ((UInt256Proof.Equality.ReferenceOperator.checked (fun a b => decide (a = b)) Extracted.profile false Extracted.program 0 1 rfl
    (fun m l r c => by simpa using ((UInt256Proof.Equality.ReferenceOperator.checked (fun a b => decide (a = b)) Extracted.profile false Extracted.program 1 2 rfl
    (fun m l r c => by simpa using (UInt256Proof.Equality.ReferenceScalar.checked Extracted.profile Extracted.program 2 3 rfl rfl rfl rfl) m l r c))) m l r c))) memory left right call

#print axioms EqualityFixture.correct
