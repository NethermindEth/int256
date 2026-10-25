import UInt256.Methods.Equality.PrimitiveProfileBindings
import Extracted
import UInt256.Methods.Equality.PrimitiveOperator
import UInt256.Methods.Equality.SignedPrimitive

/-- Primitive equality operator with checked argument order, polarity and caller-memory preservation. -/
theorem UInt256Proof.Equality.EqInt32UInt256.scalar_correctness :
    UInt256Model.Safety.ScalarOperatorContract true false CIL.Value.i32
      (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i32 _
    Extracted.profile true false Extracted.program 0 1 rfl (fun _ => rfl)
    (UInt256Proof.Equality.SignedPrimitive.checked32 Extracted.profile Extracted.program 1 2 rfl
      (UInt256Proof.Equality.UnsignedPrimitive.checked32 Extracted.profile Extracted.program 2 3 4 rfl rfl rfl rfl))

#print axioms UInt256Proof.Equality.EqInt32UInt256.scalar_correctness

theorem UInt256Proof.Equality.EqInt32UInt256.scalar_family (profile : CIL.FeatureProfile)
    (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    UInt256Model.Safety.ScalarOperatorContract true false CIL.Value.i32
      (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Model.Safety.ScalarOperatorContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
    (UInt256Proof.Equality.ProfileBindings.primitive_agreement profile vector) UInt256Proof.Equality.EqInt32UInt256.scalar_correctness

#print axioms UInt256Proof.Equality.EqInt32UInt256.scalar_family
