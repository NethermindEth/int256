import UInt256.Methods.Compare.ThreeWaySnapshot

open CIL UInt256Model
namespace UInt256Proof.Compare

theorem checked_three_way_snapshot_contract : ∀ initial left right,
    UInt256Model.Compare.ThreeWaySnapshotContract Extracted.program Extracted.entryIndex
      initial left right := three_way_snapshot_correct

theorem checked_three_way_snapshot_all_profiles_contract : ∀ profile : FeatureProfile,
    profile.Valid → ∀ initial left right,
    UInt256Model.Compare.ThreeWaySnapshotContract (reprofile Extracted.program profile)
      Extracted.entryIndex initial left right := by
  intro profile _ initial left right
  obtain ⟨fuel,final,result,execution,sign,bytes⟩ := three_way_snapshot_correct initial left right
  refine ⟨fuel,final,result,?_,sign,bytes⟩
  rw [←Extracted.profileExecution_eq profile
    (Program.profile_independent_agreement Extracted.program (by decide) _ _)]
  exact execution

#print axioms checked_three_way_snapshot_contract
#print axioms checked_three_way_snapshot_all_profiles_contract
end UInt256Proof.Compare
