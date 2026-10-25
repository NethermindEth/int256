import UInt256.Methods.StorageVector
import Extracted
import UInt256.Methods.Shift.ScalarContract

namespace UInt256Proof.Rsh

theorem vector_correctness : UInt256Model.Safety.ShiftContract .right Extracted.program 0 :=
  UInt256Proof.Shift.Safety.scalar_correctness (profile := Extracted.profile) (direction := .right)
    (storage := 1) (by rfl) (UInt256Proof.StorageVector.store_limbs_readable_contract Extracted.profile (by rfl) _ _ (by rfl))

theorem vector_family_correctness (profile : CIL.FeatureProfile)
    (storageProfile : profile.vector256Accelerated = true) : UInt256Model.Safety.ShiftContract .right (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Shift.Safety.scalar_correctness (profile := profile) (direction := .right)
    (storage := 1) (by rfl) (UInt256Proof.StorageVector.store_limbs_readable_contract profile storageProfile _ _ (by rfl))


#print axioms vector_correctness
#print axioms vector_family_correctness
end UInt256Proof.Rsh
