import Extracted
import UInt256.StorageLemmas
import UInt256.Arithmetic.Carry
open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem execute_store_contract (m : Memory) (frame fuel out : Nat) (r0 r1 r2 r3 : W64)
    (hf : Extracted.storeLimbsBody.code.length + 1 ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.storeLimbsIndex 0
      [.object out, .i64 r0, .i64 r1, .i64 r2, .i64 r3] frame [] m = some (final, []) ∧
      (∀ address, final (.byte address) = store4 m out r0 r1 r2 r3 (.byte address)) ∧
      ∀ other index, other ≠ frame → final (.local other index) = m (.local other index) := by
  have he : fuel = (fuel - (Extracted.storeLimbsBody.code.length + 1)) +
      (Extracted.storeLimbsBody.code.length + 1) := by omega
  rw [he]
  generalize fuel - (Extracted.storeLimbsBody.code.length + 1) = remaining
  simp only [cil_code, List.length_cons, List.length_nil, Nat.add_succ, Nat.add_zero]
  cil_steps write_local_read_local
  all_goals simp [store4]
  all_goals intro address; rfl

-- The postcondition exposes caller references and preserved memory only.
-- The execution budget is derived from the extracted helper body.
theorem execute_carry_contract (m : Memory) (frame fuel cslot rslot : Nat) (x y c : W64)
    (h : m (.local frame cslot) = some (.i64 c)) (hne : cslot ≠ rslot) :
    ∃ final, run Extracted.program (fuel + Extracted.addWithCarryBody.code.length + 1)
      Extracted.addWithCarryIndex 0
      [.i64 x, .i64 y, .ref (.local frame cslot), .ref (.local frame rslot)]
      (frame + 1) [] m = some (final, []) ∧
      final (.local frame cslot) = some (.i64 (carry x y c)) ∧
      final (.local frame rslot) = some (.i64 (x + y + c)) ∧
      ∀ address, (∀ i, address ≠ .local (frame + 1) i) →
        address ≠ .local frame cslot → address ≠ .local frame rslot → final address = m address := by
  have hf : frame ≠ frame + 1 := by omega
  have hf' : frame + 1 ≠ frame := Ne.symm hf
  simp only [cil_code, List.length_cons, List.length_nil, Nat.add_succ, Nat.add_zero]
  cil_steps write_local_read_local, write, read64, h, hf, hf', hne, Ne.symm hne,
    carry, add_overflow_right
  by_cases hxy : x + y < x <;> by_cases hrc : x + y + c < x + y
  all_goals
    simp only [hxy, hrc, ↓reduceIte]
    simp
    intro address hchild hca hra
    simp [hchild, hca, hra]

theorem execute_carry_contract_at (m : Memory) (frame fuel cslot rslot : Nat) (x y c : W64)
    (h : m (.local frame cslot) = some (.i64 c)) (hne : cslot ≠ rslot)
    (hf : Extracted.addWithCarryBody.code.length + 1 ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.addWithCarryIndex 0
      [.i64 x, .i64 y, .ref (.local frame cslot), .ref (.local frame rslot)] (frame + 1) [] m =
        some (final, []) ∧
      final (.local frame cslot) = some (.i64 (carry x y c)) ∧
      final (.local frame rslot) = some (.i64 (x + y + c)) ∧
      ∀ address, (∀ i, address ≠ .local (frame + 1) i) →
        address ≠ .local frame cslot → address ≠ .local frame rslot → final address = m address := by
  obtain ⟨final, he, hc, hs, hp⟩ := execute_carry_contract m frame 0 cslot rslot x y c h hne
  refine ⟨final, ?_, hc, hs, hp⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf he

end UInt256Proof
