import UInt256.Safety.RegionSuffix
import UInt256.Methods.StorageScalar
import UInt256.Methods.StorageVector

namespace UInt256Proof.Transport
open CIL.Safety

theorem scalar_storage_call_free (profile : CIL.FeatureProfile) : CallFree (UInt256Proof.StorageScalar.body profile) :=
  CallFree.of_flow (by simp [UInt256Proof.StorageScalar.body, FlowInput])

theorem vector_storage_call_free (profile : CIL.FeatureProfile) : CallFree (UInt256Proof.StorageVector.body profile) :=
  CallFree.of_flow (by
    simp [UInt256Proof.StorageVector.body, UInt256Proof.StorageVector.template, List.replicate_succ, FlowInput])

#print axioms scalar_storage_call_free
#print axioms vector_storage_call_free
end UInt256Proof.Transport
