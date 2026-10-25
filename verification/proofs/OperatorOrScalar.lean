import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.ScalarReturn

namespace UInt256Proof.OperatorOr

theorem scalar_correctness :
    UInt256Proof.Bitwise.ReturnSafety.BinaryContract (UInt256Model.Bitwise.applyBinary .or)
      Extracted.program 0 :=
  UInt256Proof.Bitwise.ReturnSafety.binary_correctness .or Extracted.profile (by rfl)
    Extracted.program 0 1 2 (by rfl) (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.OperatorOr

theorem UInt256Proof.OperatorOr.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Proof.Bitwise.ReturnSafety.BinaryContract (UInt256Model.Bitwise.applyBinary .or) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.ReturnSafety.binary_correctness .or profile disabled (CIL.reprofile Extracted.program profile) 0 1 2 (by rfl) (by rfl) (by rfl)


#print axioms UInt256Proof.OperatorOr.scalar_family_correctness
