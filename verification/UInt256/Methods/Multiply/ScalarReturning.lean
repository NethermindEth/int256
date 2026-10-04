import UInt256.Methods.Multiply.HomeWordCalls
import UInt256.Methods.Multiply.ReturnValue
open CIL UInt256Model UInt256Proof UInt256Proof.Bitwise
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

macro "multiply_scalar_return_execution " name:ident width:num order:term : command =>
  `(command|
theorem $name (memory : Memory) (input frame fuel : Nat) (a : Limbs) (word : BitVec $width)
    (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (a i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
        Extracted.entryIndex 0 (if $order then [if $width = 32 then .i32 (word.setWidth 32) else .i64 (word.setWidth 64), .object input] else [.object input, if $width = 32 then .i32 (word.setWidth 32) else .i64 (word.setWidth 64)]) frame [] memory =
          some (final, [.v256 (returnOutput a (singleWord (word.setWidth 64)))]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  simp only [BitVec.setWidth_eq, Bool.false_eq_true, Nat.reduceEqDiff, ↓reduceIte]
  by_cases top : a 1 ||| (a 2 ||| a 3) = BitVec.ofNat 64 0
  all_goals try (have av : value a = BitVec.ofNat 256 (a 0).toNat := by exact (congrArg value (singleWord_eq a (by assumption))).symm.trans (singleWord_value (a 0)))
  all_goals obtain ⟨l0, l1, l2, l3⟩ := limb_reads memory input a reads
  all_goals have vl := read256_of_limbs memory input (a 0) (a 1) (a 2) (a 3) l0 l1 l2 l3
  all_goals simp only [ne_eq, BitVec.or_eq_zero_iff] at top
  all_goals cil_execute_core l0, l1, l2, l3, vl, evalMemory, write256, unsafeAsRef, unsafeAdd, offsetValue,
    BitVec.or_eq_zero_iff, aggregate_fourWrites, readAggregate_fullWrite,
    Equality.read64_snapshot0, Equality.read64_snapshot1, Equality.read64_snapshot2, Equality.read64_snapshot3,
    Equality.readAggregate_wordWrites, Equality.readAggregate_numberWrites, Equality.read256_snapshot, decode_value with
    (first | cil_home_scalar_product_call a,a,reads,reads | cil_wide_product_call | cil_count_carry_call | cil_home_multiply_store_call)
  all_goals refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
  all_goals try unfold returnOutput
  all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only
    [scalarVector_correct, packed_single_product, singleWord_value, word64_cast, BitVec.mul_comm]
  all_goals try simp only [av]
  all_goals try (intro address; simp [*, write, writeAggregate, writeHomeBytes_caller])
)
end UInt256Proof.Multiply
