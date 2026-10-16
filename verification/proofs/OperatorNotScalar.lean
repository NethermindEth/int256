import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.NotReturn

namespace UInt256Proof.OperatorNot

theorem scalar_correctness :
    UInt256Proof.Bitwise.ReturnSafety.UnaryContract (~~~·) Extracted.program 0 :=
  UInt256Proof.Bitwise.ReturnSafety.unary_correctness Extracted.profile (by rfl)
    Extracted.program 0 1 2 (by rfl) (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.OperatorNot

theorem UInt256Proof.OperatorNot.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Proof.Bitwise.ReturnSafety.UnaryContract (~~~·) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.ReturnSafety.unary_correctness profile disabled (CIL.reprofile Extracted.program profile) 0 1 2 (by rfl) (by rfl) (by rfl)


#print axioms UInt256Proof.OperatorNot.scalar_family_correctness
