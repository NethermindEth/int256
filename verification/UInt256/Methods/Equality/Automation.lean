import UInt256.ExecutionAutomation
import UInt256.Methods.Equality.Contract
import UInt256.Methods.Equality.ScalarLemmas
import UInt256.Methods.Equality.Aggregate
import UInt256.Methods.Bitwise.Aggregate
import UInt256.Methods.Bitwise.Lemmas
import UInt256.Methods.Equality.VectorLemmas
import UInt256.Methods.Compare.Lemmas

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Equality

macro "scalar_equality_steps" ha0:term "," ha1:term "," ha2:term "," ha3:term : tactic =>
  `(tactic| cil_execute_core $ha0,$ha1,$ha2,$ha3,UInt256Model.Equality.booleanWord,
    UInt256Model.Equality.Scalar.argument,Bitwise.aggregate_fourWrites,readAggregate_wordWrites,readAggregate_numberWrites,
    read64_snapshot0,read64_snapshot1,read64_snapshot2,read64_snapshot3,decode_value,unsafeAdd,
    read256_initial_limbs,read256_writeAggregate_caller,read256_clearHome_caller,read256_write_local,evalMemory,
    intrinsic_scalar32,intrinsic_scalar64,intrinsic_equal256,intrinsic_zero256,Bitwise.intrinsic_xor256,
    BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff,
    Compare.zeroExtend32_toInt,Compare.word32_bmod64,Compare.setWidth32_toInt,write with fail)

macro "scalar_equality_execute" initial:ident "," input:ident : tactic =>
  `(tactic| (
    try have scalarCast := Compare.zeroExtend32_toInt (by assumption : W32)
    try have scalarWidth := Compare.setWidth32_toInt (by assumption : W32)
    try have scalarRemainder := Compare.word32_bmod64 (by assumption : W32)
    try have scalarNonnegative := Compare.word32_bmod64_nonnegative (by assumption : W32)
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $input:ident (inputLimbs $initial:ident $input:ident) (read64_initial $initial:ident $input:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,UInt256Model.Equality.Scalar.number]
    rw [←input_value $initial:ident $input:ident]
    scalar_equality_steps ha0,ha1,ha2,ha3
    all_goals simp (config := { failIfUnchanged := false }) only [setWidth32_eq_value]
    all_goals try (refine ⟨_,⟨rfl,?_⟩,?_⟩)
    all_goals try (solve | intro address; simp (config := { implicitDefEqProofs := false }) only [writeAggregate,writeHomeBytes_caller,clearHome_caller,write]; all_goals rfl)
    all_goals try (solve |
      try clear ha0 ha1 ha2 ha3
      try clear scalarCast
      try clear scalarWidth
      try clear scalarRemainder
      try clear scalarNonnegative
      simp_all (config := { implicitDefEqProofs := false }) [Int.ofNat_inj,value_eq_word,value_eq_word32])
    all_goals try (simp (config := { implicitDefEqProofs := false }) only [Int.ofNat_inj,value_eq_word,value_eq_word32])
    all_goals try (simp (config := { implicitDefEqProofs := false }) only [Compare.signExtend32_toNat,BitVec.toInt_eq_toNat_cond] at *)
    all_goals try (simp (config := { implicitDefEqProofs := false }) only [and_assoc, ←value_eq_word])
    all_goals try (simp_all (config := { implicitDefEqProofs := false }) only [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod,word32_mod64,zeroExtend32_toNat256,zeroExtend64_toNat256])
    all_goals scalar_equality_steps ha0,ha1,ha2,ha3
    all_goals try (simp (config := { implicitDefEqProofs := false }) only [and_assoc])
    all_goals try (refine ⟨_,rfl,?_,?_⟩)
    all_goals try (solve | intro address; simp (config := { implicitDefEqProofs := false }) only [writeAggregate,writeHomeBytes_caller,clearHome_caller,write]; all_goals rfl)
    all_goals repeat' first | (solve | omega) | (split <;> simp_all (config := { implicitDefEqProofs := false }))
    all_goals scalar_equality_steps ha0,ha1,ha2,ha3
    all_goals try (simp_all (config := { implicitDefEqProofs := false }) only [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod,word32_mod64,zeroExtend32_toNat256,zeroExtend64_toNat256])
    all_goals try (simp (config := { implicitDefEqProofs := false }) only [and_assoc])
    all_goals try (refine ⟨_,rfl,?_,?_⟩)
    all_goals try (solve | intro address; simp (config := { implicitDefEqProofs := false }) only [writeAggregate,writeHomeBytes_caller,clearHome_caller,write]; all_goals rfl)
    all_goals try clear ha0 ha1 ha2 ha3
    all_goals try clear scalarCast
    all_goals try clear scalarWidth
    all_goals try clear scalarRemainder
    all_goals try clear scalarNonnegative
    all_goals repeat' first | (solve | omega) | (split <;> simp_all (config := { implicitDefEqProofs := false }))
    all_goals repeat' first | (solve | omega) | (apply And.intro) | (intro) | (solve | rfl)
    all_goals try (simp_all (config := { implicitDefEqProofs := false }) only [decide_eq_true_iff,decide_eq_false_iff_not,Int.ofNat_inj,UInt256Proof.value_toNat])
    all_goals try (solve | simp_all (config := { implicitDefEqProofs := false }))
    all_goals omega
  ))

end UInt256Proof.Equality
