import UInt256.Methods.Multiply.HomeCalls
import UInt256.Methods.Multiply.HomeWordCalls
import UInt256.Methods.Multiply.SingleWord
import UInt256.Methods.Multiply.ReturnValue
open CIL UInt256Model UInt256Proof UInt256Proof.Bitwise
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem execute_return_entry (memory : Memory) (left right frame fuel : Nat) (a b : Limbs)
    (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
        Extracted.entryIndex 0 [.object left, .object right] frame [] memory =
          some (final, [.v256 (returnOutput a b)]) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  by_cases leftTop : a 1 ||| (a 2 ||| a 3) = BitVec.ofNat 64 0
  all_goals by_cases rightTop : b 1 ||| (b 2 ||| b 3) = BitVec.ofNat 64 0
  all_goals try (have av : value a = BitVec.ofNat 256 (a 0).toNat := by exact (congrArg value (singleWord_eq a (by assumption))).symm.trans (singleWord_value (a 0)))
  all_goals try (have bv : value b = BitVec.ofNat 256 (b 0).toNat := by exact (congrArg value (singleWord_eq b (by assumption))).symm.trans (singleWord_value (b 0)))
  all_goals obtain ⟨l0, l1, l2, l3⟩ := limb_reads memory left a leftReads
  all_goals obtain ⟨r0, r1, r2, r3⟩ := limb_reads memory right b rightReads
  all_goals have vl := read256_of_limbs memory left (a 0) (a 1) (a 2) (a 3) l0 l1 l2 l3
  all_goals have vr := read256_of_limbs memory right (b 0) (b 1) (b 2) (b 3) r0 r1 r2 r3
  all_goals simp only [ne_eq, BitVec.or_eq_zero_iff] at leftTop rightTop
  all_goals cil_execute_core l0, l1, l2, l3, r0, r1, r2, r3, vl, vr, evalMemory,
    write256, unsafeAsRef, unsafeAdd, offsetValue, BitVec.or_eq_zero_iff,
    aggregate_fourWrites, readAggregate_fullWrite with
    (first | cil_home_limb_product_call a,b,leftReads,rightReads | cil_home_scalar_product_call a,b,leftReads,rightReads | cil_wide_product_call | cil_count_carry_call | cil_home_multiply_store_call)
  all_goals first
    | refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
    | refine ⟨_, rfl, ?_⟩
  all_goals try unfold returnOutput
  all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only
    [productVector_correct, scalarVector_correct, packed_single_product, singleWord_value,
      BitVec.mul_comm]
  all_goals try simp only [av]
  all_goals try simp only [bv]
  all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [BitVec.mul_comm]
  all_goals try (intro address; simp [*, write])

end UInt256Proof.Multiply
