import UInt256.Methods.Equality.ReferenceAutomation
import UInt256.Methods.Equality.Aggregate

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Equality

macro "snapshot_split_result" : tactic =>
  `(tactic| (
    all_goals first
    | refine ⟨_,⟨rfl,?_⟩,?_⟩
    | refine ⟨_,?_,?_⟩
    | skip
    all_goals try (solve |
      intro address
      simp (config := { implicitDefEqProofs := false }) only
        [writeAggregate,writeHomeBytes_caller,clearHome_caller,write_local_read_byte]
      all_goals rfl)
  ))

macro "vector_snapshot_equality_steps" : tactic =>
  `(tactic| (
    first
    | (
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector (.equalsAll 256)) _ => true | _ => false) = true := by decide
      refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
      simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some]
      cil_execute_core read256_initial,read256_snapshot,read256_writeAggregate_caller,read256_clearHome_caller,
        read256_write_local_home,read256_write_local,
        evalMemory,UInt256Model.Equality.booleanWord,intrinsic_equal256,intrinsic_mask_eq256,
        Bitwise.intrinsic_xor256,intrinsic_zero256,BitVec.xor_eq_zero_iff with fail)
    | (
      have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
        match op with | .intrinsic (.vector (.equalsAll 128)) _ => true | _ => false) = true := by decide
      refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
      simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some]
      cil_execute_core read128_initial,read128_snapshot0,read128_snapshot1,read128_writeAggregate_caller,read128_clearHome_caller,
        read128_write_local_home,read128_write_local,
        evalMemory,unsafeAdd_byte_natural,unsafeAdd_home_one,unsafeAsRef,offsetValue,UInt256Model.Equality.booleanWord,
        intrinsic_equal128,intrinsic_xor128,intrinsic_or128,intrinsic_zero128,
        BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff with fail
      try (simp (config := { implicitDefEqProofs := false }) only [and_comm,halves_snapshot_eq_iff]))
  ))

theorem snapshot_correct (initial : Bytes) (left : Nat) (right : BitVec 256) :
    UInt256Model.Equality.SnapshotContract Extracted.program Extracted.entryIndex
      initial left right := by
  first
  | vector_snapshot_equality_steps
  | (
  obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory initial) left (inputLimbs initial left) (read64_initial initial left)
  refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
  simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some]
  rw [←input_value initial left,←value_decode right]
  simp (config := { implicitDefEqProofs := false }) only [value_eq_iff]
  cil_execute_core ha0,ha1,ha2,ha3,read64_snapshot0,read64_snapshot1,read64_snapshot2,read64_snapshot3,
    read64_writeAggregate_caller,read64_writeHomeBytes_caller,read64_clearHome_caller,
    read64_write_local_home,
    UInt256Model.Equality.booleanWord,BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff,unsafeAdd,decode_value with fail)
  snapshot_split_result
  all_goals try (rw [←input_value initial left,←value_decode right])
  all_goals try (simp (config := { implicitDefEqProofs := false }) only
    [equalityMask_zero,value_eq_iff])
  all_goals try (simp_all (config := { implicitDefEqProofs := false }) only
    [←(@BitVec.toNat_inj 32),←(@BitVec.toNat_inj 64)])
  all_goals repeat' first | (solve | omega) |
    (split <;> simp_all (config := { implicitDefEqProofs := false }) only
      [↓reduceIte,BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod,
        true_and,and_true,not_true_eq_false])
  all_goals try (refine ⟨_,?_,trivial,rfl⟩)
  all_goals try (refine ⟨_,rfl,?_⟩)
  all_goals try (solve | intro address; simp (config := { implicitDefEqProofs := false }) only [writeAggregate,writeHomeBytes_caller,clearHome_caller]; all_goals rfl)
  all_goals repeat' first | (solve | omega) | (solve | rfl) | apply And.intro | intro
  all_goals omega

end UInt256Proof.Equality
