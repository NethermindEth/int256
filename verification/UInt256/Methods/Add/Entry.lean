import UInt256.Methods.Add.EntryAutomation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem execute_entry (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addIndex)
      Extracted.addIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = addOutput m out a b (.byte address) := by
  cil_execute ha, hb with cil_scalar_call
  intro address
  apply writeBytes_congr _ _ ?_ _ _ _ address
  intro location
  simp

end UInt256Proof
