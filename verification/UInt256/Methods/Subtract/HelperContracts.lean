import UInt256.StorageContracts
import UInt256.Arithmetic.Borrow

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof

-- The postcondition exposes caller references and preserved memory only.
-- The execution budget is derived from the extracted helper body.
if_extracted Extracted.subtractWithBorrowIndex {
theorem execute_borrow_contract (m : Memory) (frame fuel cslot rslot : Nat) (x y c : W64)
    (h : m (.local frame cslot) = some (.i64 c)) (hne : cslot ≠ rslot)
    (hc : c.toNat ≤ 1) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.subtractWithBorrowIndex)
      Extracted.subtractWithBorrowIndex 0
      [.i64 x, .i64 y, .ref (.local frame cslot), .ref (.local frame rslot)]
      (frame + 1) [] m = some (final, []) ∧
      final (.local frame cslot) = some (.i64 (borrow x y c)) ∧
      final (.local frame rslot) = some (.i64 (x - y - c)) ∧
      ∀ address, (∀ other i, frame < other → address ≠ .local other i) →
        address ≠ .local frame cslot → address ≠ .local frame rslot → final address = m address := by
  have hf : frame ≠ frame + 1 := by omega
  have hf' : frame + 1 ≠ frame := Ne.symm hf
  simp only [cil_code, Nat.add_succ, Nat.add_zero]
  cil_steps write_local_read_local, write, read64, h, hf, hf', hne, Ne.symm hne,
    borrow_expression, borrow_alternative_expression, hc
  all_goals intro address hchild hca hra
  all_goals simp [hchild, hca, hra]

theorem execute_borrow_contract_at (m : Memory) (frame fuel cslot rslot : Nat) (x y c : W64)
    (h : m (.local frame cslot) = some (.i64 c)) (hne : cslot ≠ rslot)
    (hc : c.toNat ≤ 1)
    (hf : executionBound Extracted.program Extracted.subtractWithBorrowIndex ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.subtractWithBorrowIndex 0
      [.i64 x, .i64 y, .ref (.local frame cslot), .ref (.local frame rslot)] (frame + 1) [] m =
        some (final, []) ∧
      final (.local frame cslot) = some (.i64 (borrow x y c)) ∧
      final (.local frame rslot) = some (.i64 (x - y - c)) ∧
      ∀ address, (∀ other i, frame < other → address ≠ .local other i) →
        address ≠ .local frame cslot → address ≠ .local frame rslot → final address = m address := by
  obtain ⟨final, he, hc, hs, hp⟩ := execute_borrow_contract m frame 0 cslot rslot x y c h hne hc
  refine ⟨final, ?_, hc, hs, hp⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf he

}

end UInt256Proof
