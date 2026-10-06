import UInt256.Methods.Add.CarryState
import UInt256.Methods.Add.ScalarCarrySegments

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem ScalarCarryState.run_next {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} (segment : Fin 3)
    (state : ScalarCarryState original before frame left right output carryHome results (segment.val + 1))
    (extra : List Value) (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results (segment.val + 2) →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall (segment.val + 1) + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall segment.val + 1)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  have slot : frame.locals[segment.val + 4]? = some (.bytes .word64 (results index)) := by
    simpa only [index, Nat.add_assoc] using state.resultSlots index
  apply scalar_carry_segment_checked segment left right output extra frame before
    (scalarCarryValue original left right (segment.val + 1)) carryHome (results index) state.call
    state.carrySlot slot state.carryBound state.carryRead state.carryWrite (state.resultWrites index)
    (Or.inl (Ne.symm (state.carrySeparate index))) post
  intro after math
  have leftSame : inputLimb before left index = inputLimb original left index := by
    simp only [inputLimb, state.inputBytes left (by simp)]
  have rightSame : inputLimb before right index = inputLimb original right index := by
    simp only [inputLimb, state.inputBytes right (by simp)]
  change CarryPost (inputLimb before left index) (inputLimb before right index)
    (scalarCarryValue original left right index.val) carryHome (results index) before after at math
  rw [leftSame, rightSame] at math
  exact continuation after (state.advance index math)

/-- Compose all three remaining extracted calls; the final continuation receives
    all four exact result words and the mathematical final carry. -/
theorem ScalarCarryState.run_remaining {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarCarryState original before frame left right output carryHome results 1)
    (extra : List Value) (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 0 + 1)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply state.run_next 0 extra post
  intro _ second
  apply second.run_next 1 extra post
  intro _ third
  exact third.run_next 2 extra post continuation

#print axioms ScalarCarryState.run_next
#print axioms ScalarCarryState.run_remaining

end UInt256Proof.Safety
