import CIL.Safety.StepFlow
import UInt256.Methods.StorageScalar
import UInt256.Methods.StorageVector

namespace UInt256Proof.Transport

/-- The storage callees call nothing, so a region holding one whole callee is closed at its calls. -/
theorem scalar_storage_calls_nothing (profile : CIL.FeatureProfile) :
    ∀ op ∈ (UInt256Proof.StorageScalar.body profile).code, op.callees = [] := by
  simp [UInt256Proof.StorageScalar.body, CIL.Op.callees]

theorem vector_storage_calls_nothing (profile : CIL.FeatureProfile) :
    ∀ op ∈ (UInt256Proof.StorageVector.body profile).code, op.callees = [] := by
  simp [UInt256Proof.StorageVector.body, UInt256Proof.StorageVector.template, List.replicate_succ, CIL.Op.callees]

#print axioms scalar_storage_calls_nothing
#print axioms vector_storage_calls_nothing
end UInt256Proof.Transport
