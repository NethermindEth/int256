import UInt256.Methods.Compare.Automation

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Compare

theorem three_way_correct (initial : Bytes) (left right : Nat) :
    UInt256Model.Compare.ThreeWayContract Extracted.program Extracted.entryIndex
      initial left right := by
  obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory initial) left (inputLimbs initial left) (read64_initial initial left)
  obtain ⟨hb0,hb1,hb2,hb3⟩ := limb_reads (byteMemory initial) right (inputLimbs initial right) (read64_initial initial right)
  refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
  simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
  rw [←input_value initial left, ←input_value initial right]
  simp only [UInt256Proof.value_toNat]
  cil_execute_core ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3,BitVec.lt_def,write with fail
  all_goals refine ⟨_,_,⟨rfl,rfl⟩,?_,?_⟩
  all_goals try (solve | intro address; rfl)
  all_goals simp only [UInt256Model.Compare.signAgreement,BitVec.toInt_eq_toNat_cond,BitVec.toNat_ofNat]
  all_goals simp_all [←BitVec.toNat_inj]
  all_goals omega

end UInt256Proof.Compare
