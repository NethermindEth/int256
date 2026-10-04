import UInt256.ExecutionAutomation
import UInt256.Methods.Equality.Contract
import UInt256.Methods.Equality.Lemmas
import UInt256.Methods.Equality.VectorLemmas
import UInt256.Methods.Bitwise.Lemmas

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Equality

/-- Execute the actual portable vector body, then check its Boolean result. -/
macro "vector_reference_equality_execute" initial:ident "," left:ident "," right:ident : tactic =>
  `(tactic| (
    first
    | (
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector (.equalsAll 256)) _ => true | _ => false) = true := by decide
      refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
      simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
      cil_execute_core read256_initial, evalMemory, UInt256Model.Equality.booleanWord,
        intrinsic_equal256,Bitwise.intrinsic_xor256,intrinsic_zero256,BitVec.xor_eq_zero_iff with fail)
    | (
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector (.equalsAll 128)) _ => true | _ => false) = true := by decide
      refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
      simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
      cil_execute_core read128_initial, evalMemory, unsafeAdd_byte_natural, unsafeAsRef,
        offsetValue, UInt256Model.Equality.booleanWord, intrinsic_equal128,
        intrinsic_xor128, intrinsic_or128, intrinsic_zero128,
        BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff with fail
      have halves := halves_eq_iff $initial:ident $left:ident $right:ident
      try (simp only [and_comm, halves_eq_iff])
      all_goals by_cases lowEqual : halfValue $initial:ident $left:ident = halfValue $initial:ident $right:ident
      all_goals by_cases highEqual : halfValue $initial:ident ($left:ident + 16) = halfValue $initial:ident ($right:ident + 16))
    all_goals by_cases equal : byteValue $initial:ident $left:ident = byteValue $initial:ident $right:ident
    all_goals simp_all [ne_eq]
    all_goals try (first | refine ⟨_, rfl, ?_⟩ | refine ⟨_, ?_, rfl⟩)
    all_goals intro address
    all_goals simp only [write]
    all_goals rfl
  ))

macro "reference_equality_execute" initial:ident "," left:ident "," right:ident : tactic =>
  `(tactic| (
    first
    | (
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector (.equalsAll 256)) _ => true | _ => false) = true := by decide
      clear vectorBody)
    | (
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector (.equalsAll 128)) _ => true | _ => false) = true := by decide
      clear vectorBody)
    | (solve |
      obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory $initial:ident) $left:ident (inputLimbs $initial:ident $left:ident) (read64_initial $initial:ident $left:ident)
      obtain ⟨hb0,hb1,hb2,hb3⟩ := limb_reads (byteMemory $initial:ident) $right:ident (inputLimbs $initial:ident $right:ident) (read64_initial $initial:ident $right:ident)
      refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
      simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
      rw [←input_value $initial:ident $left:ident, ←input_value $initial:ident $right:ident]
      simp only [ne_eq, value_eq_iff]
      cil_execute_core ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3,UInt256Model.Equality.booleanWord,
        BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff with fail
      all_goals simp_all only [←BitVec.toNat_inj]
      all_goals repeat' first | (solve | omega) | (split <;> simp_all)
      all_goals try (refine ⟨_, rfl, ?_, ?_⟩)
      all_goals repeat' first | (solve | omega) | (solve | rfl) | apply And.intro | intro
      all_goals omega)
    all_goals vector_reference_equality_execute $initial:ident, $left:ident, $right:ident
  ))

end UInt256Proof.Equality


