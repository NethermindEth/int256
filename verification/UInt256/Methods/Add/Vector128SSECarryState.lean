import UInt256.Methods.Add.Vector128SSECarryCalls
import UInt256.Methods.Add.CarryState

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

/-- Advance the shared carry invariant through one actual SSE repair call. -/
theorem vector128_sse_carry_next {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarCarryState original before frame left right output carryHome results index.val 15 16)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results (index.val + 1) 15 16 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (172 + 7 * index.val)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (165 + 7 * index.val)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_sse_carry_segment_checked index left right output extra frame before
    (scalarCarryValue original left right index.val) carryHome (results index) state.call
    state.carrySlot (state.resultSlots index) state.carryBound state.carryRead state.carryWrite
    (state.resultWrites index) (Or.inl (Ne.symm (state.carrySeparate index))) post
  intro after math
  have leftSame : inputLimb before left index = inputLimb original left index := by
    simp only [inputLimb, state.inputBytes left (by simp)]
  have rightSame : inputLimb before right index = inputLimb original right index := by
    simp only [inputLimb, state.inputBytes right (by simp)]
  rw [leftSame, rightSame] at math
  exact continuation after (state.advance index math)

/-- All four carry calls retain the initial operands, checked private homes and
    every completed result limb, even when caller input and output views overlap. -/
theorem vector128_sse_carry_all {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarCarryState original before frame left right output carryHome results 0 15 16)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results 4 15 16 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 193 (binaryArguments left right output ++ extra)
          frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 165 (binaryArguments left right output ++ extra)
        frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_sse_carry_next 0 state extra post
  intro _ first
  apply vector128_sse_carry_next 1 first extra post
  intro _ second
  apply vector128_sse_carry_next 2 second extra post
  intro _ third
  exact vector128_sse_carry_next 3 third extra post continuation

#print axioms vector128_sse_carry_next
#print axioms vector128_sse_carry_all
end UInt256Proof.Add.Safety
