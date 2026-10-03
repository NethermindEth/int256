import UInt256.Methods.Reporting.SubtractEntry
import UInt256.Methods.Reporting.Contract

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

theorem subtract_correct (initial : Bytes) (left right out : Nat) :
    Reporting.Contract .subtract Extracted.program Extracted.entryIndex initial left right out := by
  let m := initLocals (byteMemory initial) 0 Extracted.entryBody.locals
  have ha : ∀ i : Fin 4, read64 m (.byte (left+8*i.val)) =
      some (.i64 (inputLimbs initial left i)) := by
    intro i
    simp only [m, read64_initLocals_byte]
    exact read64_initial initial left i
  have hb : ∀ i : Fin 4, read64 m (.byte (right+8*i.val)) =
      some (.i64 (inputLimbs initial right i)) := by
    intro i
    simp only [m, read64_initLocals_byte]
    exact read64_initial initial right i
  obtain ⟨final, he, hm⟩ := execute_subtract_entry_words m left right out 0 0
    (inputLimbs initial left) (inputLimbs initial right) ha hb
  refine ⟨executionBound Extracted.program Extracted.entryIndex, final, ?_, ?_⟩
  · change run Extracted.program (executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] 0 [] m = _
    simpa only [Nat.zero_add, input_value, flag, decide_eq_true_eq] using he
  · intro address
    rw [hm, store4_value]
    change writeBytes m out (value (differenceWords (inputLimbs initial left)
      (inputLimbs initial right))).toNat 32 (.byte address) = _
    rw [four_limb_difference, input_value, input_value]
    exact writeBytes_congr m (byteMemory initial)
      (by intro location; simp [m, initLocals_bytes]) _ _ _ address

#print axioms subtract_correct

end UInt256Proof.Reporting
