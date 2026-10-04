import UInt256.Methods.Compare.Automation
import UInt256.Methods.Equality.Aggregate

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Compare

theorem three_way_snapshot_correct (initial : Bytes) (left : Nat) (right : BitVec 256) :
    UInt256Model.Compare.ThreeWaySnapshotContract Extracted.program Extracted.entryIndex
      initial left right := by
  obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory initial) left (inputLimbs initial left) (read64_initial initial left)
  have number : right.toNat =
      (decode right 0).toNat + (decode right 1).toNat * 2^64 +
      (decode right 2).toNat * 2^128 + (decode right 3).toNat * 2^192 := by
    rw [←UInt256Proof.value_toNat, value_decode]
  refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
  simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some]
  rw [←input_value initial left]
  simp (config := { implicitDefEqProofs := false }) only [UInt256Proof.value_toNat,number]
  cil_execute_core ha0,ha1,ha2,ha3,Equality.read64_snapshot0,Equality.read64_snapshot1,
    Equality.read64_snapshot2,Equality.read64_snapshot3,Equality.read64_writeAggregate_caller,
    Equality.read64_writeHomeBytes_caller,BitVec.lt_def,unsafeAdd,write with fail
  all_goals refine ⟨_,_,⟨rfl,rfl⟩,?_,?_⟩
  all_goals try (solve | intro address; simp (config := { implicitDefEqProofs := false }) only [writeAggregate,writeHomeBytes_caller,clearHome_caller]; all_goals rfl)
  all_goals try (simp (config := { implicitDefEqProofs := false }) only [UInt256Model.Compare.signAgreement,BitVec.toInt_eq_toNat_cond,BitVec.toNat_ofNat])
  all_goals try (simp_all (config := { implicitDefEqProofs := false }) [←BitVec.toNat_inj])
  all_goals omega

end UInt256Proof.Compare
