import UInt256.Methods.Equality.PrimitiveProfileBindings
import Extracted
import UInt256.Methods.Equality.UnsignedPrimitive

/-- Primitive equality with finite checked return and preservation of all caller bytes. -/
theorem UInt256Proof.Equality.EqualsUInt32.scalar_correctness :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i32
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.UnsignedPrimitive.checked32
    Extracted.profile Extracted.program 0 1 2 rfl rfl rfl rfl

#print axioms UInt256Proof.Equality.EqualsUInt32.scalar_correctness

theorem UInt256Proof.Equality.EqualsUInt32.scalar_family (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i32
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Model.Safety.ScalarOperatorContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
    (UInt256Proof.Equality.ProfileBindings.primitive_agreement profile vector) UInt256Proof.Equality.EqualsUInt32.scalar_correctness

#print axioms UInt256Proof.Equality.EqualsUInt32.scalar_family
