import UInt256.Methods.Multiply.WordCalls
import UInt256.Methods.Multiply.SingleWord
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply


macro "multiply_word_dispatch_case " memory:term "," left:term "," right:term "," a:term "," b:term "," leftReads:term "," rightReads:term "," leftTop:ident "," rightTop:ident : tactic =>
  `(tactic| (
    obtain ⟨l0, l1, l2, l3⟩ := limb_reads $memory $left $a $leftReads
    obtain ⟨r0, r1, r2, r3⟩ := limb_reads $memory $right $b $rightReads
    have vl := read256_of_limbs $memory $left ($a 0) ($a 1) ($a 2) ($a 3) l0 l1 l2 l3
    have vr := read256_of_limbs $memory $right ($b 0) ($b 1) ($b 2) ($b 3) r0 r1 r2 r3
    simp only [ne_eq, BitVec.or_eq_zero_iff] at $leftTop:ident $rightTop:ident
    cil_execute_core l0, l1, l2, l3, r0, r1, r2, r3, vl, vr, evalMemory, write256_four_limbs, BitVec.or_eq_zero_iff with
      (first | cil_scalar_product_call $a,$b,$leftReads,$rightReads | cil_wide_product_call | cil_count_carry_call | cil_multiply_store_call)
    all_goals intro address
    all_goals multiply_storage_congruence
    all_goals simp_all
    done
  ))

if_extracted Extracted.entryIndex {
theorem execute_right_word_dispatch (memory : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (leftTop : a 1 ||| (a 2 ||| a 3) ≠ BitVec.ofNat 64 0)
    (rightTop : b 1 ||| (b 2 ||| b 3) = BitVec.ofNat 64 0)
    (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
        Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        (scalarLimbs a (b 0) 0) (scalarLimbs a (b 0) 1)
        (scalarLimbs a (b 0) 2) (scalarLimbs a (b 0) 3) (.byte address) := by
  multiply_word_dispatch_case memory,left,right,a,b,leftReads,rightReads,leftTop,rightTop
#print axioms UInt256Proof.Multiply.execute_right_word_dispatch
theorem execute_left_word_dispatch (memory : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (leftTop : a 1 ||| (a 2 ||| a 3) = BitVec.ofNat 64 0)
    (rightTop : b 1 ||| (b 2 ||| b 3) ≠ BitVec.ofNat 64 0)
    (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
        Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out
        (scalarLimbs b (a 0) 0) (scalarLimbs b (a 0) 1)
        (scalarLimbs b (a 0) 2) (scalarLimbs b (a 0) 3) (.byte address) := by
  multiply_word_dispatch_case memory,left,right,a,b,leftReads,rightReads,leftTop,rightTop
#print axioms UInt256Proof.Multiply.execute_left_word_dispatch
}
end UInt256Proof.Multiply
