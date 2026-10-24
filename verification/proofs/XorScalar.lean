import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.ScalarSafetyContract

namespace UInt256Proof.Xor

theorem scalar_correctness :
    UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .xor)
      Extracted.program 0 :=
  UInt256Proof.Bitwise.scalar_correctness .xor Extracted.profile (by rfl)
    Extracted.program 0 1 (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.Xor

theorem UInt256Proof.Xor.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .xor) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.scalar_correctness .xor profile disabled (CIL.reprofile Extracted.program profile) 0 1 (by rfl) (by rfl)


#print axioms UInt256Proof.Xor.scalar_family_correctness
