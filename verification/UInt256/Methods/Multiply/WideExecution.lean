import UInt256.ExecutionAutomation
import UInt256.Methods.Multiply.WordProduct
open Lean Meta Elab Command Tactic CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

@[simp↓] theorem eval_bmi2_high (a b : W64) :
    evalIntrinsic (.bmi2 .multiplyHigh64) [.i64 a, .i64 b] =
      some (.i64 (highProduct a b)) := by rfl

@[simp↓] theorem eval_arm_high (a b : W64) :
    evalIntrinsic (.armBase64 .multiplyHigh64) [.i64 a, .i64 b] =
      some (.i64 (highProduct a b)) := by rfl

elab "multiply_wide_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.wideMultiplyCandidates)
  for expression in indices do
    let expression ← liftTermElabM do whnf expression
    let .lit (.natVal index) := expression | throwError "Expected a concrete wide-product candidate"
    let number := Syntax.mkNumLit (toString index)
    let indexName := mkIdent (Name.mkSimple s!"wide_product_index_{index}")
    let theoremName := mkIdent (Name.mkSimple s!"execute_wide_product_{index}")
    let candidates := mkIdent `Extracted.wideMultiplyCandidates
    elabCommand (← `(command| if_extracted $candidates {
      @[cil_code] def $indexName : Nat := $number
      theorem $theoremName (memory : Memory) (frame fuel outputFrame outputIndex : Nat)
          (a b : W64) (_separate : outputFrame ≠ frame)
          (bound : executionBound Extracted.program $number ≤ fuel) :
          ∃ final, run Extracted.program fuel $number 0
            [.i64 a, .i64 b, .ref (.local outputFrame outputIndex)] frame [] memory =
            some (final, [.i64 (highProduct a b)]) ∧
            (∀ other index, other ≠ frame → final (.local other index) =
              write memory (.local outputFrame outputIndex) (.i64 (lowProduct a b)) (.local other index)) ∧
            ∀ address, final (.byte address) = memory (.byte address) := by
        have splitFuel : fuel = (fuel - (executionBound Extracted.program $number)) +
            (executionBound Extracted.program $number) := by omega
        rw [splitFuel]
        generalize fuel - (executionBound Extracted.program $number) = remaining
        simp only [cil_code, Nat.add_succ, Nat.add_zero]
        cil_steps write64, write, _separate, Ne.symm _separate, eval_bmi2_high, eval_arm_high
        all_goals first
          | solve | simp [lowProduct]
          | simp [← softwareLow_correct a b, ← softwareHigh_correct a b,
              softwareLow, softwareHigh, softwareUpper, softwareMiddle, softwareLower,
              digitLow, digitHigh]
        all_goals intro other index different
        all_goals simp [write, different]
    }))

multiply_wide_summaries
end UInt256Proof.Multiply
