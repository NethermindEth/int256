import UInt256.ExecutionAutomation
import UInt256.Methods.Multiply.WordProduct
open Lean Meta Elab Tactic CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

@[simp↓] theorem eval_bmi2_high (a b : W64) :
    evalIntrinsic (.bmi2 .multiplyHigh64) [.i64 a, .i64 b] =
      some (.i64 (highProduct a b)) := by rfl

@[simp↓] theorem eval_arm_high (a b : W64) :
    evalIntrinsic (.armBase64 .multiplyHigh64) [.i64 a, .i64 b] =
      some (.i64 (highProduct a b)) := by rfl

if_extracted Extracted.wideMultiplyIndex {
theorem execute_wide_product (memory : Memory) (frame fuel outputFrame outputIndex : Nat)
    (a b : W64) (_separate : outputFrame ≠ frame)
    (bound : Extracted.wideMultiplyBody.code.length + 1 ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.wideMultiplyIndex 0
      [.i64 a, .i64 b, .ref (.local outputFrame outputIndex)] frame [] memory =
      some (final, [.i64 (highProduct a b)]) ∧
      (∀ other index, other ≠ frame → final (.local other index) =
        write memory (.local outputFrame outputIndex) (.i64 (lowProduct a b)) (.local other index)) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  have splitFuel : fuel = (fuel - (Extracted.wideMultiplyBody.code.length + 1)) +
      (Extracted.wideMultiplyBody.code.length + 1) := by omega
  rw [splitFuel]
  generalize fuel - (Extracted.wideMultiplyBody.code.length + 1) = remaining
  simp only [cil_code, Nat.add_succ, Nat.add_zero]
  cil_steps write64, write, _separate, Ne.symm _separate, eval_bmi2_high, eval_arm_high
  all_goals first
    | solve | simp [lowProduct]
    | simp [← softwareLow_correct a b, ← softwareHigh_correct a b,
        softwareLow, softwareHigh, softwareUpper, softwareMiddle, softwareLower,
        digitLow, digitHigh]
  all_goals intro other index different
  all_goals simp [write, different]
}
end UInt256Proof.Multiply
