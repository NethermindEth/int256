import UInt256.Methods.Subtract.BorrowState
import UInt256.Methods.Subtract.ScalarBorrowSegments

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

theorem ScalarBorrowState.run_next {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} (segment : Fin 3)
    (state : ScalarBorrowState original before frame left right output borrowHome results (segment.val + 1))
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results (segment.val + 2) →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall (segment.val + 1) + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall segment.val + 1)
        (binaryArguments left right output) frame [] before = .ok (result, returned) ∧ post result returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  have slot : frame.locals[segment.val + 3]? = some (.bytes .word64 (results index)) := by
    simpa only [index, Nat.add_assoc] using state.resultSlots index
  apply scalar_borrow_segment_checked segment left right output frame before
    (scalarBorrowValue original left right (segment.val + 1)) borrowHome (results index) state.call
    state.borrowSlot slot state.borrowBound state.borrowRead state.borrowWrite (state.resultWrites index)
    (Or.inl (Ne.symm (state.borrowSeparate index))) post
  intro after math
  have leftSame : inputLimb before left index = inputLimb original left index := by
    simp only [inputLimb, state.inputBytes left (by simp)]
  have rightSame : inputLimb before right index = inputLimb original right index := by
    simp only [inputLimb, state.inputBytes right (by simp)]
  change BorrowPost (inputLimb before left index) (inputLimb before right index)
    (scalarBorrowValue original left right index.val) borrowHome (results index) before after at math
  rw [leftSame, rightSame] at math
  exact continuation after (state.advance index math)

/-- Compose all three remaining extracted calls; the final continuation receives
    all four exact result words and the mathematical final borrow. -/
theorem ScalarBorrowState.run_remaining {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarBorrowState original before frame left right output borrowHome results 1)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 0 + 1)
        (binaryArguments left right output) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply state.run_next 0 post
  intro _ second
  apply second.run_next 1 post
  intro _ third
  exact third.run_next 2 post continuation

#print axioms ScalarBorrowState.run_next
#print axioms ScalarBorrowState.run_remaining

end UInt256Proof.Subtract.Safety
