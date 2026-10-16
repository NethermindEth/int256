import UInt256.Methods.StorageScalar
import Extracted
import UInt256.Methods.Shift.ScalarContract

namespace UInt256Proof.Lsh

theorem scalar_correctness : UInt256Model.Safety.ShiftContract .left Extracted.program 0 :=
  UInt256Proof.Shift.Safety.scalar_correctness (profile := Extracted.profile) (direction := .left)
    (storage := 1) (by rfl) (UInt256Proof.StorageScalar.store_limbs_readable_contract Extracted.profile (by rfl) _ _ (by rfl))

theorem scalar_family_correctness (profile : CIL.FeatureProfile)
    (storageProfile : profile.vector256Accelerated = false) : UInt256Model.Safety.ShiftContract .left (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Shift.Safety.scalar_correctness (profile := profile) (direction := .left)
    (storage := 1) (by rfl) (UInt256Proof.StorageScalar.store_limbs_readable_contract profile storageProfile _ _ (by rfl))


#print axioms scalar_correctness
#print axioms scalar_family_correctness
end UInt256Proof.Lsh
