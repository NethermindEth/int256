import UInt256.ExecutionAutomation
import UInt256.Methods.Equality.Contract
import UInt256.Methods.Equality.ScalarLemmas
import UInt256.Methods.Equality.Aggregate
import UInt256.Methods.Bitwise.Aggregate
import UInt256.Methods.Compare.Lemmas

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Equality

macro "scalar_equality_execute" initial:ident "," input:ident : tactic =>
  `(tactic| (
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $input:ident (inputLimbs $initial:ident $input:ident) (read64_initial $initial:ident $input:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,UInt256Model.Equality.Scalar.number]
    rw [←input_value $initial:ident $input:ident]
    simp only [UInt256Proof.value_toNat]
    cil_execute_core ha0,ha1,ha2,ha3,UInt256Model.Equality.booleanWord,
      UInt256Model.Equality.Scalar.argument,Bitwise.aggregate_fourWrites,
      read64_snapshot0,read64_snapshot1,read64_snapshot2,read64_snapshot3,decode_value,unsafeAdd,
      BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff,Compare.zeroExtend32_toNat,
      Compare.setWidth32_toInt,write with fail
    all_goals try (simp only [Compare.signExtend32_toNat,BitVec.toInt_eq_toNat_cond] at *)
    all_goals try (simp_all only [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod])
    all_goals try (simp only [and_assoc])
    all_goals try (refine ⟨_,rfl,?_,?_⟩)
    all_goals try (solve | intro address; simp only [writeAggregate,writeHomeBytes_caller,clearHome_caller])
    all_goals repeat' first | (solve | omega) | (split at * <;> simp_all)
    all_goals repeat' first | (solve | omega) | (apply And.intro) | (intro) | (solve | rfl)
    all_goals omega
  ))

end UInt256Proof.Equality
