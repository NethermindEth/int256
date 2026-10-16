import CIL.ProfileEquivalence
import Extracted
import UInt256.Methods.Bitwise.ScalarReturn

namespace UInt256Proof.OperatorXor

theorem scalar_correctness :
    UInt256Proof.Bitwise.ReturnSafety.BinaryContract (UInt256Model.Bitwise.applyBinary .xor)
      Extracted.program 0 :=
  UInt256Proof.Bitwise.ReturnSafety.binary_correctness .xor Extracted.profile (by rfl)
    Extracted.program 0 1 2 (by rfl) (by rfl) (by rfl)

#print axioms scalar_correctness
end UInt256Proof.OperatorXor

theorem UInt256Proof.OperatorXor.scalar_family_correctness (profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :
    UInt256Proof.Bitwise.ReturnSafety.BinaryContract (UInt256Model.Bitwise.applyBinary .xor) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.ReturnSafety.binary_correctness .xor profile disabled (CIL.reprofile Extracted.program profile) 0 1 2 (by rfl) (by rfl) (by rfl)


#print axioms UInt256Proof.OperatorXor.scalar_family_correctness
