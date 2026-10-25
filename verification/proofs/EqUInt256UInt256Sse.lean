import UInt256.Methods.Equality.ReferenceProfileBindings
import Extracted
import UInt256.Methods.Equality.ReferenceSseWrapper
import UInt256.Methods.Equality.ReferenceOperator

 theorem UInt256Proof.Equality.EqUInt256UInt256.sse_correctness :
    UInt256Model.Safety.ReadOnlyContract (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0)) Extracted.program 0 2 := by
  apply (by simpa using UInt256Proof.Equality.ReferenceOperator.readOnly_contract (fun a b => decide (a = b)) Extracted.program 0)
  intro memory left right call
  simpa using UInt256Proof.Equality.ReferenceOperator.checked (fun a b => decide (a = b)) Extracted.profile false Extracted.program 0 1 rfl
    (fun m l r c => by simpa using UInt256Proof.Equality.ReferenceSseWrapper.checked Extracted.profile Extracted.program 1 2 rfl rfl rfl rfl m l r c) memory left right call
#print axioms UInt256Proof.Equality.EqUInt256UInt256.sse_correctness



theorem UInt256Proof.Equality.EqUInt256UInt256.sse_family (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    UInt256Model.Safety.ReadOnlyContract (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0)) (CIL.reprofile Extracted.program profile) 0 2 :=
  UInt256Model.Safety.ReadOnlyContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
    (UInt256Proof.Equality.ProfileBindings.reference_agreement profile vector sse) UInt256Proof.Equality.EqUInt256UInt256.sse_correctness

#print axioms UInt256Proof.Equality.EqUInt256UInt256.sse_family
