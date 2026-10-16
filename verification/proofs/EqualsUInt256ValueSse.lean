import UInt256.Methods.Equality.ReferenceProfileBindings
import Extracted
import UInt256.Methods.Equality.ReferenceSseWrapper
import UInt256.Methods.ValueForwarder32

 theorem UInt256Proof.Equality.EqualsUInt256Value.sse_correctness :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.ValueForwarder32.encode
      (fun left right => .i32 (if left = right then 1 else 0)) Extracted.program 0 := by
  apply UInt256Proof.ValueForwarder32.checked Extracted.profile Extracted.program 0 1 true
    (fun left right => if left = right then 1 else 0)
  · intro left right _; split <;> simp
  · rfl
  · exact UInt256Proof.Equality.ReferenceSseWrapper.checked Extracted.profile Extracted.program 1 2 rfl rfl rfl rfl
#print axioms UInt256Proof.Equality.EqualsUInt256Value.sse_correctness


theorem UInt256Proof.Equality.EqualsUInt256Value.sse_family (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.ValueForwarder32.encode
      (fun left right => .i32 (if left = right then 1 else 0)) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Model.Safety.ReadOnlyScalarContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
    (UInt256Proof.Equality.ProfileBindings.reference_agreement profile vector sse) UInt256Proof.Equality.EqualsUInt256Value.sse_correctness

#print axioms UInt256Proof.Equality.EqualsUInt256Value.sse_family
