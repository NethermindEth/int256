import UInt256.Methods.Equality.ReferenceProfileBindings
import Extracted
import UInt256.Methods.Equality.ValueScalar

/-- By-value UInt256 equality, including private-copy lifetime and caller-byte preservation. -/
theorem UInt256Proof.Equality.EqualsUInt256Value.scalar_correctness :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.Equality.ValueScalar.encode
      (fun left right => .i32 (if left = right then 1 else 0)) Extracted.program 0 :=
  UInt256Proof.Equality.ValueScalar.checked Extracted.profile Extracted.program 0 1 2 rfl rfl rfl rfl rfl

#print axioms UInt256Proof.Equality.EqualsUInt256Value.scalar_correctness

theorem UInt256Proof.Equality.EqualsUInt256Value.scalar_family (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.Equality.ValueScalar.encode
      (fun left right => .i32 (if left = right then 1 else 0)) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Model.Safety.ReadOnlyScalarContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
    (UInt256Proof.Equality.ProfileBindings.reference_agreement profile vector sse) UInt256Proof.Equality.EqualsUInt256Value.scalar_correctness

#print axioms UInt256Proof.Equality.EqualsUInt256Value.scalar_family
