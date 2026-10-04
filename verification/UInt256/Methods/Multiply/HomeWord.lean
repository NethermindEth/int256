import UInt256.Methods.Multiply.HomeStorageCalls
import UInt256.Methods.Multiply.ScalarUnits
import UInt256.Arithmetic.Carry
open Lean Meta Elab Command Tactic CIL UInt256Model UInt256Proof UInt256Proof.Bitwise
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

@[irreducible] def scalarVector (a : Limbs) (word : W64) : CIL.Vector.V256 :=
  CIL.Vector.pack256 (scalarLimbs a word 0) (scalarLimbs a word 1)
    (scalarLimbs a word 2) (scalarLimbs a word 3)

theorem productVector_correct (a b : Limbs) : productVector a b = value a * value b := by
  unfold productVector
  rw [pack_limbs_value, product_limbs_correct]

theorem scalarVector_correct (a : Limbs) (word : W64) :
    scalarVector a word = value a * BitVec.ofNat 256 word.toNat := by
  unfold scalarVector
  rw [pack_limbs_value, scalar_limbs_correct]

elab "multiply_home_word_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.wordOperationCandidates)
  for expression in indices do
    let .lit (.natVal index) ← liftTermElabM (whnf expression) | throwError "Expected concrete candidate"
    for kind in ["0", "1", "large"] do
      let number := Syntax.mkNumLit (toString index)
      let name := mkIdent (Name.mkSimple s!"execute_home_word_{kind}_{index}")
      let candidates := mkIdent `Extracted.wordOperationCandidates
      let domain ← if kind == "0" then `(term| word = BitVec.ofNat 64 0)
        else if kind == "1" then `(term| word = BitVec.ofNat 64 1)
        else `(term| BitVec.ofNat 64 1 < word)
      elabCommand (← `(command| if_extracted $candidates {
        theorem $name (memory : Memory) (input frame fuel outFrame outKind outIndex : Nat)
            (a : Limbs) (word : W64) (unit : $domain)
            (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (a i))) :
            ∃ final, run Extracted.program (fuel + executionBound Extracted.program $number) $number 0
                [.object input, .i64 word, .ref (.home outFrame outKind outIndex 0)] frame [] memory =
                  some (final, []) ∧
              readAggregate final outFrame outKind outIndex = some (.v256 (scalarVector a word)) ∧
              ∀ address, final (.byte address) = memory (.byte address) := by
          obtain ⟨r0, r1, r2, r3⟩ := limb_reads memory input a reads
          have snapshot := read256_of_limbs memory input (a 0) (a 1) (a 2) (a 3) r0 r1 r2 r3
          try subst word
          cil_execute_core r0, r1, r2, r3, snapshot, evalMemory, write256, unsafeAsRef, unsafeAdd,
            extend_choice, sumHigh_flag, aggregate_fourWrites, readAggregate_fullWrite with
            (first | cil_wide_product_call | cil_count_carry_call | cil_home_multiply_store_call)
          all_goals unfold scalarVector
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [scalarLimbs_zero, scalarLimbs_one]
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only
            [scalarLimbs_zero, scalarLimbs_one, scalarLimbs, Fin.val_zero, Fin.val_one,
              Fin.val_two, show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte,
              scalarCarry, lowProduct, BitVec.mul_comm]
      }))
  
multiply_home_word_summaries
end UInt256Proof.Multiply
