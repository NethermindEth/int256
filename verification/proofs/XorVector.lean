import Extracted
import CIL.ProfileEquivalence
import UInt256.Methods.Bitwise.VectorSafety

namespace UInt256Proof.Xor

theorem vector_correctness : UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .xor) Extracted.program 0 :=
  UInt256Proof.Bitwise.VectorSafety.correctness Extracted.profile (by rfl) .xor Extracted.program 0 1 (by rfl) (by rfl)

theorem vector_family_correctness (profile : CIL.FeatureProfile)
    (enabled : profile.vector256Accelerated = true) :
    UInt256Model.Safety.WrappingBinaryContract (UInt256Model.Bitwise.applyBinary .xor) (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Bitwise.VectorSafety.correctness profile enabled .xor (CIL.reprofile Extracted.program profile) 0 1 (by rfl) (by rfl)

#print axioms vector_correctness
#print axioms vector_family_correctness
end UInt256Proof.Xor
