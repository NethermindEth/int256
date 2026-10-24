import Extracted
import CIL.ProfileEquivalence
import UInt256.Methods.Bitwise.VectorReturn

namespace UInt256Proof.OperatorNot

theorem vector_correctness : UInt256Proof.Bitwise.ReturnSafety.UnaryContract (~~~·) Extracted.program 0 :=
  UInt256Proof.Bitwise.VectorReturn.unary_correctness Extracted.profile (by rfl) Extracted.program 0 1 2 (by rfl) (by rfl) (by rfl)

theorem vector_family_correctness (profile : CIL.FeatureProfile)
    (enabled : profile.vector256Accelerated = true) :
    UInt256Proof.Bitwise.ReturnSafety.UnaryContract (~~~·) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.VectorReturn.unary_correctness profile enabled (CIL.reprofile Extracted.program profile) 0 1 2 (by rfl) (by rfl) (by rfl)

#print axioms vector_correctness
#print axioms vector_family_correctness
end UInt256Proof.OperatorNot
