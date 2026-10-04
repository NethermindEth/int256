import UInt256.Methods.Multiply.Entry
import UInt256.Methods.Multiply.Contract
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem multiply_correct (initial : Bytes) (left right out : Nat) :
    Contract Extracted.program Extracted.entryIndex initial left right out := by
  let memory := initLocals (byteMemory initial) 0 Extracted.entryBody.locals
  have leftReads : ∀ i : Fin 4,
      read64 memory (.byte (left+8*i.val)) = some (.i64 (inputLimbs initial left i)) := by
    intro i
    simp only [memory, read64_initLocals_byte]
    exact read64_initial initial left i
  have rightReads : ∀ i : Fin 4,
      read64 memory (.byte (right+8*i.val)) = some (.i64 (inputLimbs initial right i)) := by
    intro i
    simp only [memory, read64_initLocals_byte]
    exact read64_initial initial right i
  obtain ⟨final, execution, bytes⟩ := execute_entry memory left right out 0 0
    (inputLimbs initial left) (inputLimbs initial right) leftReads rightReads
  refine ⟨executionBound Extracted.program Extracted.entryIndex, final, ?_, ?_⟩
  · change run Extracted.program (executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] 0 [] memory = some (final, [])
    simpa only [Nat.zero_add] using execution
  · simp only [multiplyOutput] at bytes
    rw [input_value, input_value] at bytes
    intro address
    rw [bytes]
    exact writeBytes_congr memory (byteMemory initial)
      (by intro location; simp [memory, initLocals_bytes]) _ _ _ address

theorem checked_contract : ∀ (initial : Bytes) (left right out : Nat),
    Contract Extracted.program Extracted.entryIndex initial left right out := multiply_correct

end UInt256Proof.Multiply
