import UInt256.Methods.Add.Entry
import UInt256.Methods.Add.Contract

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem add_correct (initial : Bytes) (left right out : Nat) :
    Contract Extracted.program Extracted.entryIndex initial left right out := by
  let m := initLocals (byteMemory initial) 0 Extracted.entryBody.locals
  have ha : ∀ i : Fin 4, read64 m (.byte (left+8*i.val)) = some (.i64 (inputLimbs initial left i)) := by
    intro i
    simp only [m, read64_initLocals_byte]
    exact read64_initial initial left i
  have hb : ∀ i : Fin 4, read64 m (.byte (right+8*i.val)) = some (.i64 (inputLimbs initial right i)) := by
    intro i
    simp only [m, read64_initLocals_byte]
    exact read64_initial initial right i
  obtain ⟨final, he, hm⟩ := execute_entry m left right out 0 0
    (inputLimbs initial left) (inputLimbs initial right) ha hb
  refine ⟨executionBound Extracted.program Extracted.entryIndex, final, ?_, ?_⟩
  · change run Extracted.program (executionBound Extracted.program Extracted.entryIndex) Extracted.entryIndex 0 [.object left, .object right, .object out] 0 [] m = some (final, [])
    simpa only [Nat.zero_add] using he
  · simp only [addOutput] at hm
    rw [input_value, input_value] at hm
    intro address
    rw [hm]
    exact writeBytes_congr m (byteMemory initial)
      (by intro location; simp [m, initLocals_bytes]) _ _ _ address

end UInt256Proof
