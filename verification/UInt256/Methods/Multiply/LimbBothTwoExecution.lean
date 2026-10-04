import UInt256.Methods.Multiply.Calls
import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ZeroProducts
open Lean Meta Elab Command Tactic CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

elab "multiply_limb_BothTwo_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.limbProductCandidates)
  for expression in indices do
    let expression ← liftTermElabM do whnf expression
    if ← liftTermElabM do isDefEq expression (mkConst `Extracted.entryIndex) then continue
    let .lit (.natVal index) := expression | throwError "Expected a concrete limb candidate"
    let number := Syntax.mkNumLit (toString index)
    let name := mkIdent (Name.mkSimple s!"execute_limbs_BothTwo_{index}")
    let candidates := mkIdent `Extracted.limbProductCandidates
    elabCommand (← `(command| if_extracted $candidates {
      theorem $name (memory : Memory) (left right out frame fuel : Nat) (a b : Limbs)
          (upper : a 2 = 0 ∧ a 3 = 0)
          (rightUpper : b 2 = 0 ∧ b 3 = 0)
          (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) = some (.i64 (a i)))
          (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) = some (.i64 (b i))) :
          ∃ final, run Extracted.program (fuel + executionBound Extracted.program $number) $number 0
              [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
            ∀ address, final (.byte address) = store4 memory out
              (productLimbs a b 0) (productLimbs a b 1) (productLimbs a b 2) (productLimbs a b 3)
              (.byte address) := by
        obtain ⟨a2, a3⟩ := upper
        obtain ⟨b2, b3⟩ := rightUpper
        obtain ⟨l0, l1, l2, l3⟩ := limb_reads memory left a leftReads
        obtain ⟨r0, r1, r2, r3⟩ := limb_reads memory right b rightReads
        have vl := read256_of_limbs memory left (a 0) (a 1) (a 2) (a 3) l0 l1 l2 l3
        have vr := read256_of_limbs memory right (b 0) (b 1) (b 2) (b 3) r0 r1 r2 r3
        cil_execute_core l0, l1, l2, l3, r0, r1, r2, r3, vl, vr, evalMemory, unsafeAsRef, digitLow_shift32, narrow_low_correct, narrow_low_split, narrow_low_tail with
          (first | cil_wide_product_call | cil_count_carry_call | cil_multiply_store_call)
        all_goals simp only [productLimbs, Fin.val_zero, Fin.val_one, Fin.val_two,
          show (0 : W64) = BitVec.ofNat 64 0 from rfl,
          show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte,
          firstColumn, secondColumn, topWords, column, List.foldl_cons, List.foldl_nil,
          columnStep, List.sum_cons, List.sum_nil, BitVec.add_zero, BitVec.add_assoc]
        all_goals simp only [show (0 : W64) = BitVec.ofNat 64 0 from rfl, a2, a3, b2, b3, lowProduct_zero_left, lowProduct_zero_right, highProduct_zero_left, highProduct_zero_right, BitVec.add_zero, BitVec.zero_add, countCarry, sumHigh_zero_left, sumHigh_zero_right]
        all_goals intro address
        all_goals simp only [store4, lowProduct, BitVec.toNat_add, BitVec.toNat_mul,
          BitVec.toNat_zero, show (2 : Nat)^64 = 18446744073709551616 from by decide,
          Nat.add_mod, Nat.mod_mod, Nat.add_assoc, Nat.add_zero, Nat.zero_mod, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
        all_goals simp only [Nat.mod_mod]
        all_goals apply writeBytes_congr
        all_goals intro address
        all_goals apply writeBytes_congr
        all_goals intro address
        all_goals apply writeBytes_congr
        all_goals intro address
        all_goals apply writeBytes_congr
        all_goals simp [*, lowProduct]
    }))

multiply_limb_BothTwo_summaries
end UInt256Proof.Multiply




