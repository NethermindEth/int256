import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.ScalarSafetyContract

namespace UInt256Proof.Or

theorem scalar_correctness :
    UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .or)
      Extracted.program 0 :=
  UInt256Proof.Bitwise.scalar_correctness .or Extracted.profile (by rfl)
    Extracted.program 0 1 (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.Or

theorem UInt256Proof.Or.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .or) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.scalar_correctness .or profile disabled (CIL.reprofile Extracted.program profile) 0 1 (by rfl) (by rfl)


#print axioms UInt256Proof.Or.scalar_family_correctness
