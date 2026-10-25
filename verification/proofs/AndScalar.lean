import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.ScalarSafetyContract

namespace UInt256Proof.And

theorem scalar_correctness :
    UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .and)
      Extracted.program 0 :=
  UInt256Proof.Bitwise.scalar_correctness .and Extracted.profile (by rfl)
    Extracted.program 0 1 (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.And

theorem UInt256Proof.And.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .and) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.scalar_correctness .and profile disabled (CIL.reprofile Extracted.program profile) 0 1 (by rfl) (by rfl)


#print axioms UInt256Proof.And.scalar_family_correctness
