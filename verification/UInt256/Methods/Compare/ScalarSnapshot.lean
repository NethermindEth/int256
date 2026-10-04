import UInt256.Methods.Compare.Automation
import UInt256.Methods.Equality.Aggregate

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Compare

theorem scalar_snapshot_correct (initial : Bytes) (word : W64) (right : BitVec 256) :
    UInt256Model.Compare.ScalarSnapshotContract Extracted.program Extracted.entryIndex
      .lessEqual initial (.u64 word) right := by
  have number : right.toNat =
      (decode right 0).toNat + (decode right 1).toNat * 2^64 +
      (decode right 2).toNat * 2^128 + (decode right 3).toNat * 2^192 := by
    rw [←UInt256Proof.value_toNat, value_decode]
  refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
  simp only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,
    UInt256Model.Compare.holds,UInt256Model.Equality.Scalar.number,Int.ofNat_le]
  cil_execute_core Equality.read64_snapshot0,Equality.read64_snapshot1,Equality.read64_snapshot2,Equality.read64_snapshot3,UInt256Model.Equality.Scalar.argument,
    UInt256Model.Equality.booleanWord,BitVec.lt_def,unsafeAdd,write with fail
  all_goals try (simp_all only [number,←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod])
  all_goals try (simp only [and_assoc])
  all_goals try (refine ⟨_,rfl,?_,?_⟩)
  all_goals try (solve | intro address; simp only [writeAggregate,writeHomeBytes_caller,clearHome_caller])
  all_goals repeat' first | (solve | omega) | (split at * <;> simp_all)
  all_goals repeat' first | (solve | omega) | (apply And.intro) | (intro) | (solve | rfl)
  all_goals omega

end UInt256Proof.Compare
