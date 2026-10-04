import UInt256.Methods.Multiply.Calls
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply


macro "multiply_single_word_case " memory:term "," left:term "," right:term "," a:term "," b:term "," leftReads:term "," rightReads:term : tactic =>
  `(tactic| (
    obtain ⟨l0, l1, l2, l3⟩ := limb_reads $memory $left (fun i => if i = 0 then $a else 0) $leftReads
    obtain ⟨r0, r1, r2, r3⟩ := limb_reads $memory $right (fun i => if i = 0 then $b else 0) $rightReads
    simp only [↓reduceIte, Fin.isValue, Fin.reduceEq] at l0 l1 l2 l3 r0 r1 r2 r3
    cil_execute_core l0, l1, l2, l3, r0, r1, r2, r3 with
      (first | cil_wide_product_call | cil_multiply_store_call)
    all_goals intro address
    all_goals multiply_storage_congruence
    all_goals simp_all
    done
  ))

if_extracted Extracted.entryIndex {
theorem execute_single_words (memory : Memory) (left right out frame fuel : Nat)
    (a b : W64)
    (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) =
      some (.i64 (if i = 0 then a else 0)))
    (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) =
      some (.i64 (if i = 0 then b else 0))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = store4 memory out (lowProduct a b) (highProduct a b) 0 0 (.byte address) := by
  multiply_single_word_case memory,left,right,a,b,leftReads,rightReads
#print axioms UInt256Proof.Multiply.execute_single_words
}
end UInt256Proof.Multiply
