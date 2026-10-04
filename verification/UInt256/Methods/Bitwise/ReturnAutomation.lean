import UInt256.Methods.Bitwise.Automation
import UInt256.Methods.Equality.Aggregate

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Bitwise

macro "bitwise_return_preservation" : tactic =>
  `(tactic| (
    intro address
    simp (config := { implicitDefEqProofs := false }) only [writeAggregate,writeHomeBytes_caller,clearHome_caller,write_local_read_byte]
    all_goals rfl
  ))

macro "bitwise_return_finish" : tactic =>
  `(tactic| (
    first
    | refine ⟨_,⟨rfl,?_⟩,?_⟩
    | refine ⟨_,rfl,?_⟩
    all_goals first
    | (solve |
      apply congrArg value
      funext i
      rcases i with ⟨i,bound⟩
      have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
      rcases cases with h|h|h|h <;> subst i <;> rfl)
    | (solve | bitwise_return_preservation)
  ))

macro "vector_bitwise_return_execute" : tactic =>
  `(tactic| (
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector _) _ => true | _ => false) = true := by decide
      refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
      simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,UInt256Model.Bitwise.applyBinary]
      cil_execute_core read256_initial,Equality.read256_writeAggregate_caller,Equality.read256_clearHome_caller,
        read256_write_local,evalMemory,write256,intrinsic_and256,intrinsic_or256,intrinsic_xor256,intrinsic_not256,
        UInt256Proof.Bitwise.readAggregate_fullWrite with fail
      try (simp (config := { implicitDefEqProofs := false }) only [←BitVec.toNat_and,←BitVec.toNat_or,←BitVec.toNat_xor,full_not_number,UInt256Proof.Bitwise.readAggregate_fullWrite])
      cil_execute_core read256_initial,Equality.read256_writeAggregate_caller,Equality.read256_clearHome_caller,
        read256_write_local,evalMemory,write256,intrinsic_and256,intrinsic_or256,intrinsic_xor256,intrinsic_not256,
        UInt256Proof.Bitwise.readAggregate_fullWrite with fail
      all_goals try (refine ⟨_,rfl,?_⟩)
      all_goals bitwise_return_preservation
  ))

macro "binary_bitwise_return_execute" initial:ident "," left:ident "," right:ident ","
    valueLemma:term : tactic =>
  `(tactic| (
    first
    | (solve | vector_bitwise_return_execute)
    | (
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $left:ident (inputLimbs $initial:ident $left:ident) (read64_initial $initial:ident $left:ident)
    obtain ⟨hb0,hb1,hb2,hb3⟩ := limb_reads (byteMemory $initial:ident) $right:ident (inputLimbs $initial:ident $right:ident) (read64_initial $initial:ident $right:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,UInt256Model.Bitwise.applyBinary]
    rw [←input_value $initial:ident $left:ident,←input_value $initial:ident $right:ident,←$valueLemma]
    cil_execute_core ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3,aggregate_fourWrites,
      Equality.readAggregate_wordWrites,Equality.readAggregate_numberWrites,Equality.readAggregate_highWordWrites,decode_value,
      Equality.read64_writeAggregate_caller,Equality.read64_writeHomeBytes_caller,
      Equality.read64_clearHome_caller,read64_write_local_byte,
      evalMemory,write256,unsafeAdd with fail
    try (simp (config := { implicitDefEqProofs := false }) only [←BitVec.toNat_xor,←BitVec.toNat_and,←BitVec.toNat_or,aggregate_fourWrites,
      Equality.readAggregate_wordWrites,Equality.readAggregate_highWordWrites,decode_value,Option.bind_some])
    cil_execute_core ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3,aggregate_fourWrites,
      Equality.readAggregate_wordWrites,Equality.readAggregate_numberWrites,Equality.readAggregate_highWordWrites,decode_value,
      Equality.read64_writeAggregate_caller,Equality.read64_writeHomeBytes_caller,
      Equality.read64_clearHome_caller,read64_write_local_byte,
      evalMemory,write256,unsafeAdd,aggregate_snapshot_after_write,UInt256Proof.Bitwise.readAggregate_fullWrite with fail
    try (simp (config := { implicitDefEqProofs := false }) only [Equality.readAggregate_highWordWrites,decode_value,Option.bind_some])
    cil_execute_core evalMemory,write256,unsafeAdd with fail
    bitwise_return_finish
  )))

macro "not_bitwise_return_execute" initial:ident "," input:ident : tactic =>
  `(tactic| (
    first
    | (solve | vector_bitwise_return_execute)
    | (
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $input:ident (inputLimbs $initial:ident $input:ident) (read64_initial $initial:ident $input:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some]
    rw [←input_value $initial:ident $input:ident,←value_not]
    cil_execute_core ha0,ha1,ha2,ha3,aggregate_fourWrites,
      Equality.readAggregate_wordWrites,Equality.readAggregate_numberWrites,Equality.readAggregate_highWordWrites,decode_value,
      Equality.read64_writeAggregate_caller,Equality.read64_writeHomeBytes_caller,
      Equality.read64_clearHome_caller,read64_write_local_byte,evalMemory,write256,unsafeAdd with fail
    try (simp (config := { implicitDefEqProofs := false }) only [word_not_number,word_not_xor_number,aggregate_fourWrites,
      Equality.readAggregate_wordWrites,Equality.readAggregate_highWordWrites,decode_value,Option.bind_some])
    cil_execute_core ha0,ha1,ha2,ha3,aggregate_fourWrites,
      Equality.readAggregate_wordWrites,Equality.readAggregate_numberWrites,Equality.readAggregate_highWordWrites,decode_value,
      Equality.read64_writeAggregate_caller,Equality.read64_writeHomeBytes_caller,
      Equality.read64_clearHome_caller,read64_write_local_byte,evalMemory,write256,unsafeAdd,
      aggregate_snapshot_after_write,UInt256Proof.Bitwise.readAggregate_fullWrite with fail
    try (simp (config := { implicitDefEqProofs := false }) only [Equality.readAggregate_highWordWrites,UInt256Proof.Bitwise.readAggregate_fullWrite,decode_value,Option.bind_some])
    cil_execute_core evalMemory,write256,unsafeAdd,UInt256Proof.Bitwise.readAggregate_fullWrite with fail
    try (simp (config := { implicitDefEqProofs := false }) only [word_not_number,BitVec.ofNat_toNat])
    bitwise_return_finish
  )))

end UInt256Proof.Bitwise

