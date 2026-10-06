import UInt256.Methods.Subtract.Vector128BorrowCalls
import UInt256.Methods.Subtract.BorrowState

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Advance the shared borrow invariant through one actual vector repair call. -/
theorem vector128_borrow_next {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarBorrowState original before frame left right output borrowHome results index.val 11 12)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results (index.val + 1) 11 12 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (87 + 7 * index.val)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (80 + 7 * index.val)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_borrow_segment_checked index left right output extra frame before
    (scalarBorrowValue original left right index.val) borrowHome (results index) state.call
    state.borrowSlot (state.resultSlots index) state.borrowBound state.borrowRead state.borrowWrite
    (state.resultWrites index) (Or.inl (Ne.symm (state.borrowSeparate index))) post
  intro after math
  have leftSame : inputLimb before left index = inputLimb original left index := by
    simp only [inputLimb, state.inputBytes left (by simp)]
  have rightSame : inputLimb before right index = inputLimb original right index := by
    simp only [inputLimb, state.inputBytes right (by simp)]
  rw [leftSame, rightSame] at math
  exact continuation after (state.advance index math)

/-- All four borrow calls retain the initial operands, checked private homes and
    every completed result limb, even when caller input and output views overlap. -/
theorem vector128_borrow_all {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarBorrowState original before frame left right output borrowHome results 0 11 12)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results 4 11 12 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 108 (binaryArguments left right output ++ extra)
          frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 80 (binaryArguments left right output ++ extra)
        frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_borrow_next 0 state extra post
  intro _ first
  apply vector128_borrow_next 1 first extra post
  intro _ second
  apply vector128_borrow_next 2 second extra post
  intro _ third
  exact vector128_borrow_next 3 third extra post continuation

#print axioms vector128_borrow_next
#print axioms vector128_borrow_all
end UInt256Proof.Subtract.Safety
