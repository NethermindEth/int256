import Extracted
import UInt256.StorageLemmas

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof

if_extracted Extracted.storeLimbsIndex {
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
  simp only [cil_code, Nat.add_succ, Nat.add_zero]
  cil_steps write_local_read_local
  all_goals simp [store4]
  all_goals intro address; rfl

}

end UInt256Proof
