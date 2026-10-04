import UInt256.Methods.Multiply.DispatchCalls
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

macro "multiply_multi_limb_case " memory:term "," left:term "," right:term "," a:term "," b:term "," leftReads:term "," rightReads:term "," leftTop:ident "," rightTop:ident : tactic =>
  `(tactic| (
    obtain ⟨l0, l1, l2, l3⟩ := limb_reads $memory $left $a $leftReads
    obtain ⟨r0, r1, r2, r3⟩ := limb_reads $memory $right $b $rightReads
    simp only [ne_eq, BitVec.or_eq_zero_iff] at $leftTop:ident $rightTop:ident
    cil_execute_core l0, l1, l2, l3, r0, r1, r2, r3, BitVec.or_eq_zero_iff with
      (first | cil_limb_product_call $a,$b,$leftReads,$rightReads | cil_wide_product_call | cil_count_carry_call | cil_multiply_store_call)
    all_goals try (with_reducible rw [productLimbs_comm $b $a])
    all_goals intro address
    all_goals multiply_storage_congruence
    all_goals try (with_reducible rfl)
    all_goals try (with_reducible assumption)
    all_goals try (intro callerAddress; simp only [UInt256Proof.initLocals_bytes, UInt256Proof.write_local_read_byte])
    done
  ))

if_extracted Extracted.entryIndex {
theorem execute_multi_limb_dispatch (memory : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (leftTop : a 1 ||| (a 2 ||| a 3) ≠ BitVec.ofNat 64 0)
    (rightTop : b 1 ||| (b 2 ||| b 3) ≠ BitVec.ofNat 64 0)
    (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
        Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        (productLimbs a b 0) (productLimbs a b 1) (productLimbs a b 2) (productLimbs a b 3) (.byte address) := by
  multiply_multi_limb_case memory,left,right,a,b,leftReads,rightReads,leftTop,rightTop
#print axioms UInt256Proof.Multiply.execute_multi_limb_dispatch
}
end UInt256Proof.Multiply
