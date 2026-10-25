import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.ScalarReturn

namespace UInt256Proof.OperatorAnd

theorem scalar_correctness :
    UInt256Proof.Bitwise.ReturnSafety.BinaryContract (UInt256Model.Bitwise.applyBinary .and)
      Extracted.program 0 :=
  UInt256Proof.Bitwise.ReturnSafety.binary_correctness .and Extracted.profile (by rfl)
    Extracted.program 0 1 2 (by rfl) (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.OperatorAnd

theorem UInt256Proof.OperatorAnd.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Proof.Bitwise.ReturnSafety.BinaryContract (UInt256Model.Bitwise.applyBinary .and) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.ReturnSafety.binary_correctness .and profile disabled (CIL.reprofile Extracted.program profile) 0 1 2 (by rfl) (by rfl) (by rfl)


#print axioms UInt256Proof.OperatorAnd.scalar_family_correctness
