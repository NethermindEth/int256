import UInt256.Methods.Equality.PrimitiveProfileBindings
import Extracted
import UInt256.Methods.Equality.VectorPrimitiveWrapper

/-- Primitive equality with finite checked return and preservation of all caller bytes. -/
theorem UInt256Proof.Equality.EqualsUInt64.vector_correctness :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i64
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.VectorPrimitiveWrapper.checked64
    Extracted.profile Extracted.program 0 1 rfl rfl rfl

#print axioms UInt256Proof.Equality.EqualsUInt64.vector_correctness


theorem UInt256Proof.Equality.EqualsUInt64.vector_family (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i64
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Model.Safety.ScalarOperatorContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
    (UInt256Proof.Equality.ProfileBindings.primitive_agreement profile vector) UInt256Proof.Equality.EqualsUInt64.vector_correctness

#print axioms UInt256Proof.Equality.EqualsUInt64.vector_family
