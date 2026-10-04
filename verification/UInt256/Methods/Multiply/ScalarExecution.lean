import UInt256.Methods.Multiply.Calls
import UInt256.Methods.Multiply.ScalarValue
import UInt256.Arithmetic.Carry
open Lean Meta Elab Command Tactic CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply
elab "multiply_word_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.wordOperationCandidates)
  for expression in indices do
    let expression ← liftTermElabM do whnf expression
    let .lit (.natVal index) := expression | throwError "Expected a concrete word-operation candidate"
    let number := Syntax.mkNumLit (toString index)
    let name := mkIdent (Name.mkSimple s!"execute_word_{index}")
    let candidates := mkIdent `Extracted.wordOperationCandidates
    elabCommand (← `(command| if_extracted $candidates {
      theorem $name (memory : Memory) (input out frame fuel : Nat) (a : Limbs) (word : W64)
          (large : BitVec.ofNat 64 1 < word)
          (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (a i))) :
          ∃ final, run Extracted.program (fuel + executionBound Extracted.program $number) $number 0
              [.object input, .i64 word, .object out] frame [] memory = some (final, []) ∧
            ∀ address, final (.byte address) = store4 memory out
              (scalarLimbs a word 0) (scalarLimbs a word 1) (scalarLimbs a word 2) (scalarLimbs a word 3)
              (.byte address) := by
        obtain ⟨r0, r1, r2, r3⟩ := limb_reads memory input a reads
        have outside : ¬ word ≤ BitVec.ofNat 64 1 := by
          simp only [BitVec.le_def, BitVec.lt_def] at *
          omega
        cil_execute_core r0, r1, r2, r3, outside, extend_choice, sumHigh_flag with
          (first | cil_wide_product_call | cil_multiply_store_call)
        all_goals simp only [scalarLimbs, Fin.val_zero, Fin.val_one, Fin.val_two,
          show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte, scalarCarry]
        all_goals intro address
        all_goals simp only [store4, lowProduct, BitVec.toNat_add, BitVec.toNat_mul,
          show (2 : Nat)^64 = 18446744073709551616 from by decide, Nat.mul_comm,
          Nat.add_mod, Nat.mod_mod, Nat.add_assoc]
        all_goals simp only [Nat.mod_mod]
        all_goals apply writeBytes_congr
        all_goals intro address
        all_goals apply writeBytes_congr
        all_goals intro address
        all_goals apply writeBytes_congr
        all_goals intro address
        all_goals apply writeBytes_congr
        all_goals simp_all [lowProduct, scalarCarry, sumHigh_flag]
    }))
multiply_word_summaries
end UInt256Proof.Multiply
