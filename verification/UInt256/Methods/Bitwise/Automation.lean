import UInt256.ExecutionAutomation
import UInt256.Methods.Bitwise.Contract
import UInt256.Methods.Bitwise.Lemmas
import UInt256.Methods.Bitwise.Aggregate

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Bitwise

/-- The supplied representation lemma connects full-width mathematics to limbs. -/
macro "binary_bitwise_execute" initial:ident "," left:ident "," right:ident ","
    _out:ident "," valueLemma:term : tactic =>
  `(tactic| (
    first
    | (solve |
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector _) _ => true | _ => false) = true := by decide
      refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
      simp only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,UInt256Model.Bitwise.applyBinary]
      cil_execute_core read256_initial,intrinsic_and256,intrinsic_or256,intrinsic_xor256,evalMemory,write256,unsafeAdd with fail
      all_goals first | (solve | rfl) | (solve | refine ⟨_,rfl,?_⟩; intro address; rfl))
    | (
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $left:ident (inputLimbs $initial:ident $left:ident) (read64_initial $initial:ident $left:ident)
    obtain ⟨hb0,hb1,hb2,hb3⟩ := limb_reads (byteMemory $initial:ident) $right:ident (inputLimbs $initial:ident $right:ident) (read64_initial $initial:ident $right:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
    simp only [UInt256Model.Bitwise.applyBinary]
    rw [←input_value $initial:ident $left:ident, ←input_value $initial:ident $right:ident, ←$valueLemma]
    cil_execute_core ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3,aggregate_fourWrites,
      evalMemory,write256,unsafeAdd with fail
    try (simp only [←BitVec.toNat_xor,←BitVec.toNat_and,←BitVec.toNat_or,aggregate_fourWrites,Option.bind_some])
    cil_execute_core evalMemory,write256,unsafeAdd with fail
    all_goals intro address
    all_goals apply writeBytes_equal
    all_goals try rfl
    all_goals try (solve | intro location; simp only [writeAggregate,writeHomeBytes_caller,clearHome_caller])
    all_goals intro location
  )))

end UInt256Proof.Bitwise
