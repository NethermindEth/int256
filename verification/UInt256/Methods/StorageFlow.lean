import UInt256.Safety.RegionSuffix
import UInt256.Methods.StorageScalar
import UInt256.Methods.StorageVector

namespace UInt256Proof.Transport
open CIL.Safety

private theorem call_free_of_classified (body : CIL.Method)
    (classified : ∀ op ∈ body.code, (Supported op ∧ FlowInput 0 (fun _ => False) op) ∨ StorageExtra op) :
    CallFree body := by
  intro op member pc args frame stack memory action executed
  rcases classified op member with ⟨supported, targets⟩ | extra
  · exact supported_flow _ op supported pc args frame stack memory action 0 _ (by omega) targets executed
  · exact storage_extra_flow _ op extra pc args frame stack memory action executed

theorem scalar_storage_call_free (profile : CIL.FeatureProfile) : CallFree (UInt256Proof.StorageScalar.body profile) := by
  apply call_free_of_classified
  simp only [UInt256Proof.StorageScalar.body, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first
    | (solve | simp)
    | (apply Or.inr; constructor)
    | (apply Or.inl; constructor
       · first | exact .arg _ | exact .ret | (apply Supported.memory; constructor)
       · trivial)

theorem vector_storage_call_free (profile : CIL.FeatureProfile) : CallFree (UInt256Proof.StorageVector.body profile) := by
  apply call_free_of_classified
  simp only [UInt256Proof.StorageVector.body, UInt256Proof.StorageVector.template, Bool.false_eq_true, ite_false,
    List.forall_mem_append, List.forall_mem_cons, List.replicate_succ, List.replicate_zero]
  repeat' apply And.intro
  all_goals first
    | (solve | simp)
    | (apply Or.inr; constructor)
    | (apply Or.inl; constructor
       · first | exact .arg _ | exact .ret | (apply Supported.memory; constructor)
       · trivial)

#print axioms scalar_storage_call_free
#print axioms vector_storage_call_free
end UInt256Proof.Transport
