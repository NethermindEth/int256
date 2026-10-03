import UInt256.ExecutionAutomation
import UInt256.Methods.Multiply.CountCarry
open Lean Meta Elab Tactic CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

if_extracted Extracted.carryCountIndex {
theorem execute_count_carry (memory : Memory) (frame fuel outputFrame outputIndex : Nat)
    (a b count : W64) (separate : outputFrame ≠ frame)
    (read : memory (.local outputFrame outputIndex) = some (.i64 count))
    (bound : Extracted.carryCountBody.code.length + 1 ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.carryCountIndex 0
      [.i64 a, .i64 b, .ref (.local outputFrame outputIndex)] frame [] memory =
      some (final, [.i64 (a + b)]) ∧
      (∀ other index, other ≠ frame → final (.local other index) =
        write memory (.local outputFrame outputIndex) (.i64 (countCarry a b count)) (.local other index)) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  have splitFuel : fuel = (fuel - (Extracted.carryCountBody.code.length + 1)) +
      (Extracted.carryCountBody.code.length + 1) := by omega
  rw [splitFuel]
  generalize fuel - (Extracted.carryCountBody.code.length + 1) = remaining
  simp only [cil_code, Nat.add_succ, Nat.add_zero]
  cil_steps write, read64, separate, Ne.symm separate, read
  by_cases overflow : a + b < a
  all_goals simp only [countCarry, ← sumHigh_flag a b, overflow, ↓reduceIte]
  all_goals intro other index different
  all_goals simp [different]
}
end UInt256Proof.Multiply
