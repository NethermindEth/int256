import UInt256.Methods.Add.Vector128SSERepairStart

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_sse_carry_segment (disabled : Extracted.profile.advSimd = false) (segment : Fin 4) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (a b : BitVec 64) (carryHome resultHome : Reference)
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right)
    (leftRead : ∀ rest, instruction (.field segment)
      (.reference (.address left) :: rest) memory = .ok (memory, .scalar (.i64 a) :: rest))
    (rightRead : ∀ rest, instruction (.field segment)
      (.reference (.address right) :: rest) memory = .ok (memory, .scalar (.i64 b) :: rest))
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[segment.val + 16]? = some (.bytes .word64 resultHome))
    (carryFormed : form memory carryHome = .ok carryHome)
    (resultFormed : form memory resultHome = .ok resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (171 + 7 * segment.val)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (165 + 7 * segment.val)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  first
  | solve | simp [Extracted.profile] at disabled
  |
    obtain ⟨segment, bound⟩ := segment
    have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      dsimp at leftRead rightRead resultSlot
      first
      | change frame.locals[16]? = some (.bytes .word64 resultHome) at resultSlot
      | change frame.locals[17]? = some (.bytes .word64 resultHome) at resultSlot
      | change frame.locals[18]? = some (.bytes .word64 resultHome) at resultSlot
      | change frame.locals[19]? = some (.bytes .word64 resultHome) at resultSlot
      repeat'
        first
        | exact continuation
        | simp (config := { failIfUnchanged := false })
          apply run_next_exists post (by rfl : Extracted.program[vector128Index]? = some vector128Body) (by rfl)
          simp (config := { implicitDefEqProofs := false })
              [cil_code, step, checkedValue, formValue, leftFormed, rightFormed,
                carryFormed, resultFormed, carrySlot, resultSlot, localAddress, leftRead, rightRead,
                pureArity, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩


#print axioms vector128_sse_carry_segment
end UInt256Proof.Add.Safety
