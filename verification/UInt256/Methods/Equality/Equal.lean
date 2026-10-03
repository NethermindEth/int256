import UInt256.ExecutionAutomation
import UInt256.Methods.Equality.Contract
import UInt256.Methods.Equality.Lemmas
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Equality
theorem equal_correct (initial : Bytes) (left right : Nat) :
    UInt256Model.Equality.Contract Extracted.program Extracted.entryIndex initial left right := by
  obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory initial) left (inputLimbs initial left) (read64_initial initial left)
  obtain ⟨hb0,hb1,hb2,hb3⟩ := limb_reads (byteMemory initial) right (inputLimbs initial right) (read64_initial initial right)
  refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
  simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
  rw [←input_value initial left, ←input_value initial right]
  simp only [value_eq_iff]
  cil_execute_core ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3,UInt256Model.Equality.booleanWord,
    BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff with fail
  all_goals simp_all only [←BitVec.toNat_inj]
  all_goals repeat' first | (solve | omega) | (split <;> simp_all)
  all_goals try (refine ⟨_, rfl, ?_, ?_⟩)
  all_goals repeat' first | (solve | omega) | (solve | rfl) | apply And.intro | intro
  all_goals omega
end UInt256Proof.Equality
