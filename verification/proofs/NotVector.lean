import Extracted
import CIL.ProfileEquivalence
import UInt256.Methods.Bitwise.NotVectorSafety

namespace UInt256Proof.Not

theorem vector_correctness : UInt256Model.Safety.WrappingUnaryContract (~~~·) Extracted.program 0 :=
  UInt256Proof.Bitwise.NotVectorSafety.correctness Extracted.profile (by rfl) Extracted.program 0 1 (by rfl) (by rfl)

theorem vector_family_correctness (profile : CIL.FeatureProfile)
    (enabled : profile.vector256Accelerated = true) :
    UInt256Model.Safety.WrappingUnaryContract (~~~·) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.NotVectorSafety.correctness profile enabled (CIL.reprofile Extracted.program profile) 0 1 (by rfl) (by rfl)

#print axioms vector_correctness
#print axioms vector_family_correctness
end UInt256Proof.Not
