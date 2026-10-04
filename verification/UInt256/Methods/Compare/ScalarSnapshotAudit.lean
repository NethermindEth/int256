import UInt256.Methods.Compare.ScalarSnapshot
open CIL UInt256Model
namespace UInt256Proof.Compare
theorem checked_scalar_snapshot_contract : ∀ initial word right,
 UInt256Model.Compare.ScalarSnapshotContract Extracted.program Extracted.entryIndex .lessEqual initial (.u64 word) right := scalar_snapshot_correct
theorem checked_scalar_snapshot_all_profiles_contract : ∀ profile : FeatureProfile,
 profile.Valid → ∀ initial word right,
 UInt256Model.Compare.ScalarSnapshotContract (reprofile Extracted.program profile) Extracted.entryIndex .lessEqual initial (.u64 word) right := by
 intro profile _ initial word right
 obtain ⟨fuel,final,execution,bytes⟩ := scalar_snapshot_correct initial word right
 refine ⟨fuel,final,?_,bytes⟩
 rw [←Extracted.profileExecution_eq profile (Program.profile_independent_agreement Extracted.program (by decide) _ _)]
 exact execution
#print axioms checked_scalar_snapshot_contract
#print axioms checked_scalar_snapshot_all_profiles_contract
end UInt256Proof.Compare
