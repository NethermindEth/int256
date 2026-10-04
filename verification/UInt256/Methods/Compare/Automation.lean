import UInt256.ExecutionAutomation
import UInt256.Methods.Compare.Contract
import UInt256.Methods.Compare.Lemmas
import UInt256.Methods.Compare.VectorAutomation

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Compare

/-- Prove the selected body against its independently stated numerical comparison. -/
macro "comparison_execute" initial:ident "," left:ident "," right:ident : tactic =>
  `(tactic| (
    first
    | (solve | native_comparison_execute $initial:ident,$left:ident,$right:ident)
    | (solve | portable_comparison_execute $initial:ident,$left:ident,$right:ident)
    | (
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $left:ident
      (inputLimbs $initial:ident $left:ident) (read64_initial $initial:ident $left:ident)
    obtain ⟨hb0,hb1,hb2,hb3⟩ := limb_reads (byteMemory $initial:ident) $right:ident
      (inputLimbs $initial:ident $right:ident) (read64_initial $initial:ident $right:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
    simp only [UInt256Model.Compare.holds, Int.ofNat_lt, Int.ofNat_le]
    rw [← input_value $initial:ident $left:ident, ← input_value $initial:ident $right:ident]
    simp only [UInt256Proof.value_toNat]
    cil_execute_core ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3,UInt256Model.Equality.booleanWord,
      BitVec.lt_def, write, read256_initial_limbs, read256_write_local, evalMemory,
      intrinsic_extract256, UInt256Proof.Equality.value_pack with fail
    all_goals try (simp only [and_assoc])
    all_goals try (simp_all only [← BitVec.toNat_inj])
    all_goals try (refine ⟨_, rfl, ?_, ?_⟩)
    all_goals try (solve | intro address; rfl)
    all_goals repeat' first | (solve | omega) | (split at * <;> simp_all)
    all_goals repeat' first | (solve | omega) | (apply And.intro) | (intro) | (solve | rfl)
    all_goals omega

  )))

/-- Primitive operand direction and signedness come from the explicit contract. -/
macro "scalar_comparison_execute" initial:ident "," input:ident : tactic =>
  `(tactic| (
    try have scalarCast := zeroExtend32_toInt (by assumption : W32)
    try have scalarWidth := setWidth32_toInt (by assumption : W32)
    try have scalarRemainder := word32_bmod64 (by assumption : W32)
    try have scalarNonnegative := word32_bmod64_nonnegative (by assumption : W32)
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $input:ident (inputLimbs $initial:ident $input:ident) (read64_initial $initial:ident $input:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
    simp only [UInt256Model.Compare.holds, UInt256Model.Equality.Scalar.number, Int.ofNat_lt, Int.ofNat_le]
    rw [←input_value $initial:ident $input:ident]
    simp only [UInt256Proof.value_toNat]
    cil_execute_core ha0,ha1,ha2,ha3,UInt256Model.Equality.booleanWord,
      UInt256Model.Equality.Scalar.argument, BitVec.lt_def,
      zeroExtend32_toNat,zeroExtend32_toInt,setWidth32_toInt,word32_bmod64,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), write with fail
    all_goals try (simp only [and_assoc])
    all_goals try (simp only [signExtend32_toNat,
      BitVec.toInt_eq_toNat_cond] at *)
    all_goals try (simp_all only [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod])
    all_goals cil_execute_core ha0,ha1,ha2,ha3,UInt256Model.Equality.booleanWord,
      UInt256Model.Equality.Scalar.argument,BitVec.lt_def,zeroExtend32_toNat,
      zeroExtend32_toInt,setWidth32_toInt,word32_bmod64,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),write with fail
    all_goals try (simp only [and_assoc])
    all_goals try (refine ⟨_,rfl,?_,?_⟩)
    all_goals try (solve | intro address; rfl)
    all_goals repeat' first | (solve | omega) | (split at * <;> simp_all)
    all_goals cil_execute_core ha0,ha1,ha2,ha3,UInt256Model.Equality.booleanWord,
      UInt256Model.Equality.Scalar.argument,BitVec.lt_def,zeroExtend32_toNat,
      zeroExtend32_toInt,setWidth32_toInt,word32_bmod64,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),write with fail
    all_goals try (simp_all only [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod])
    all_goals try (simp only [and_assoc])
    all_goals try (refine ⟨_,rfl,?_,?_⟩)
    all_goals try (solve | intro address; rfl)
    all_goals repeat' first | (solve | omega) | (split at * <;> simp_all)
    all_goals repeat' first | (solve | omega) | (apply And.intro) | (intro) | (solve | rfl)
    all_goals omega
  ))

end UInt256Proof.Compare
