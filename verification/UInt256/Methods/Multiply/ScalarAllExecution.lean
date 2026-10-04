import UInt256.Methods.Multiply.ScalarExecution
import UInt256.Methods.Multiply.Scalar0Execution
import UInt256.Methods.Multiply.Scalar1Execution
open Lean Meta Elab Command CIL UInt256Model UInt256Proof
namespace UInt256Proof.Multiply
elab "multiply_all_word_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.wordOperationCandidates)
  for expression in indices do
    let .lit (.natVal index) ← liftTermElabM (whnf expression) | throwError "Expected a concrete word candidate"
    let zero := `UInt256Proof.Multiply |>.str s!"execute_word_0_{index}"
    let one := `UInt256Proof.Multiply |>.str s!"execute_word_1_{index}"
    let large := `UInt256Proof.Multiply |>.str s!"execute_word_{index}"
    unless (← getEnv).contains zero && (← getEnv).contains one && (← getEnv).contains large do continue
    let zero := mkIdent zero
    let one := mkIdent one
    let large := mkIdent large
    let name := mkIdent (Name.mkSimple s!"execute_word_all_{index}")
    let number := Syntax.mkNumLit (toString index)
    elabCommand (← `(command|
      theorem $name (memory : Memory) (input out frame fuel : Nat) (a : Limbs) (word : W64)
          (reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (a i))) :
          ∃ final, run Extracted.program (fuel + executionBound Extracted.program $number) $number 0
              [.object input, .i64 word, .object out] frame [] memory = some (final, []) ∧
            ∀ address, final (.byte address) = store4 memory out
              (scalarLimbs a word 0) (scalarLimbs a word 1) (scalarLimbs a word 2) (scalarLimbs a word 3)
              (.byte address) := by
        by_cases unitZero : word = BitVec.ofNat 64 0
        · exact $zero memory input out frame fuel a word unitZero reads
        by_cases unitOne : word = BitVec.ofNat 64 1
        · exact $one memory input out frame fuel a word unitOne reads
        apply $large memory input out frame fuel a word _ reads
        have notZero : word.toNat ≠ 0 := by
          intro same
          apply unitZero
          apply BitVec.eq_of_toNat_eq
          simpa using same
        have notOne : word.toNat ≠ 1 := by
          intro same
          apply unitOne
          apply BitVec.eq_of_toNat_eq
          simpa using same
        simp only [BitVec.lt_def, BitVec.toNat_ofNat]
        omega))
multiply_all_word_summaries
end UInt256Proof.Multiply
