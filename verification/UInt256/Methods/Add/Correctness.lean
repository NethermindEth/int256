import UInt256.Methods.Add.Execution
import UInt256.Methods.Add.Contract

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem execute_entry (m final : Memory) (left right out frame fuel : Nat) (flag : W32)
    (h : run Extracted.program (fuel + 500) 1 0
      [.object left, .object right, .object out, .i32 0] (frame+1) []
      (initLocals m (frame+1) Extracted.method1.locals) = some (final, [.i32 flag])) :
    run Extracted.program (fuel + 507) 0 0 [.object left, .object right, .object out]
      frame [] m = some (final, []) := by
  have hc := h
  simp [Extracted.program, Extracted.method0] at hc
  iterate 7
    rw [run]
    simp [step, Extracted.program, Extracted.method0, truth]
  rw [hc]
  simp only [Option.bind_some]
  rw [run]
  simp [step]
  rw [run]
  simp [step]

theorem add_correct (initial : Bytes) (left right out : Nat) :
    Contract Extracted.program initial left right out := by
  let m0 := initLocals (byteMemory initial) 0 Extracted.method0.locals
  let m1 := initLocals m0 1 Extracted.method1.locals
  have ha : ∀ i : Fin 4, read64 m1 (.byte (left+8*i.val)) = some (.i64 (inputLimbs initial left i)) := by
    intro i
    simp only [m1, m0, read64_initLocals_byte]
    exact read64_initial initial left i
  have hb : ∀ i : Fin 4, read64 m1 (.byte (right+8*i.val)) = some (.i64 (inputLimbs initial right i)) := by
    intro i
    simp only [m1, m0, read64_initLocals_byte]
    exact read64_initial initial right i
  obtain ⟨final, flag, he, hm⟩ := execute_scalar m1 left right out 1 205
    (inputLimbs initial left) (inputLimbs initial right) ha hb
  have hentry := execute_entry m0 final left right out 0 5 flag he
  refine ⟨final, ?_, ?_⟩
  · change run Extracted.program 512 0 0 [.object left, .object right, .object out] 0 [] m0 = some (final, [])
    exact hentry
  · rw [input_value, input_value] at hm
    intro address
    rw [hm]
    exact writeBytes_congr m1 (byteMemory initial)
      (by intro location; simp [m1, m0, initLocals_bytes]) _ _ _ address

end UInt256Proof
