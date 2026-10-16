import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.NotScalar

namespace UInt256Proof.Not

theorem scalar_correctness :
    UInt256Model.Safety.WrappingUnaryContract (~~~·) Extracted.program 0 :=
  UInt256Proof.Bitwise.not_correctness Extracted.profile (by rfl)
    Extracted.program 0 1 (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.Not

theorem UInt256Proof.Not.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Model.Safety.WrappingUnaryContract (~~~·) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.not_correctness profile disabled (CIL.reprofile Extracted.program profile) 0 1 (by rfl) (by rfl)


#print axioms UInt256Proof.Not.scalar_family_correctness
