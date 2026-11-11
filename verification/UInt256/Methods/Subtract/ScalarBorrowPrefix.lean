import UInt256.Methods.Subtract.BorrowHelper
import UInt256.Methods.Subtract.ScalarBorrowSegments
import UInt256.Methods.Add.InputWords
import UInt256.Methods.Subtract.ScalarSafetyPrefix

/-! The large-operand route of the extracted scalar body: the private borrow word is cleared
    and four checked borrow calls produce the result words and the final borrow. -/

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Profile

/-- Load the next limb pair and both private homes, call the borrow helper and advance the
    chain invariant by one result word. -/
theorem scalar_borrow_run_next (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} (segment : Fin 3)
    (state : ScalarBorrowState (program := Extracted.program) original before frame left right output borrowHome results (segment.val + 1))
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState (program := Extracted.program) original after frame left right output borrowHome results (segment.val + 2) →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall (segment.val + 1) + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall segment.val + 1)
        (binaryArguments left right output) frame [] before = .ok (result, returned) ∧ post result returned := by
  have resultSlot : frame.locals[segment.val + 3]? =
      some (.bytes .word64 (results ⟨segment.val + 1, by omega⟩)) := by
    simpa only [Nat.add_assoc] using state.resultSlots ⟨segment.val + 1, by omega⟩
  have leftRead := state.call.input_field_instruction (by simp : left ∈ [left, right])
    ⟨segment.val + 1, by omega⟩
  have rightRead := state.call.input_field_instruction (by simp : right ∈ [left, right])
    ⟨segment.val + 1, by omega⟩
  have leftSame (index : Fin 4) : inputLimb before left index = inputLimb original left index := by
    simp only [inputLimb, state.inputBytes left (by simp)]
  have rightSame (index : Fin 4) :
      inputLimb before right index = inputLimb original right index := by
    simp only [inputLimb, state.inputBytes right (by simp)]
  simp only [leftSame] at leftRead
  simp only [rightSame] at rightRead
  have tail := scalar_indexed_borrow contract ⟨segment.val + 1, by omega⟩
    (binaryArguments left right output) frame before
    (inputLimb original left ⟨segment.val + 1, by omega⟩)
    (inputLimb original right ⟨segment.val + 1, by omega⟩)
    (scalarBorrowValue original left right (segment.val + 1)) borrowHome
    (results ⟨segment.val + 1, by omega⟩) state.call.1.1
    state.flagBound state.flagRead state.flagWrite (state.resultWrites ⟨segment.val + 1, by omega⟩)
    (Or.inl (Ne.symm (state.flagSeparate ⟨segment.val + 1, by omega⟩))) post
    (fun after formed world framed math =>
      continuation after (state.advance ⟨segment.val + 1, by omega⟩ math formed world framed))
  have fl := state.call.input_formed (reference := left) (by simp)
  have fr := state.call.input_formed (reference := right) (by simp)
  have fb := access_reference_valid _ _ _ _ _ state.flagWrite
  have fo := access_reference_valid _ _ _ _ _ (state.resultWrites ⟨segment.val + 1, by omega⟩)
  have borrowSlot := state.flagSlot
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    conv in (scalarBorrowCall _) => cbv
    cil_contract_steps [found, binaryArguments, fl, fr, fb, fo, borrowSlot, resultSlot,
      leftRead, rightRead] until tail

/-- Execute the scalar body through its complete large-operand borrow chain: clear the
    private borrow word, then make the four checked borrow calls. The continuation receives
    the four checked result words before output stores. -/
theorem scalar_general_borrows (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) (original entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (large : inputLimb original right 1 ||| inputLimb original right 2 |||
      inputLimb original right 3 ≠ BitVec.ofNat 64 0)
    (post : Memory → List Value → Prop)
    (continuation : ∀ borrowHome results after,
      ScalarBorrowState (program := Extracted.program) original after frame left right output borrowHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply scalar_right_prefix_checked original entered left right output frame call setup homes post
  intro before saved preserved beforeCall authority _
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  obtain ⟨borrowHome, borrowSlot, _, _, initialWrite⟩ := homes.word_at 1 0 (by rfl)
  have writable := authority.access initialWrite (enteredWF.access_bound initialWrite)
  have writableHomes := homes.writable
  have beforeFormed := beforeCall.1.1
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have adv : scalarBody.profile.advSimd = false := by rfl
  have sse : scalarBody.profile.sse42 = false := by rfl
  conv in scalarFirstDecision => cbv
  have valid := beforeCall.1
  cil_contract_steps (snapshots := saved) [found, large, adv, sse, binaryArguments,
    call.input_words_kept preserved left (by simp)]
  have cleared : read storedLocal borrowHome 8 1 = .ok (numberBytes 0 8) := by
    simpa [localWidth] using write_readback _ _ _ _ _ localWrite
  -- The chain invariant comes from the allocated homes; caller views need no separation.
  obtain ⟨results, state⟩ : ∃ results, ScalarBorrowState (program := Extracted.program) original
      storedLocal frame left right output borrowHome results 0 :=
    UInt256Proof.AddSubtract.Safety.RippleState.initial
      Extracted.program (wordKinds scalarLocalSpecs) 1 0 original entered storedLocal frame
      frame.locals (by intro index; rfl) (fun i => by
        have specified : scalarLocalSpecs[1 + i.val]? = some (some 0) := by
          obtain ⟨i, bound⟩ := i
          have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
          rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
        obtain ⟨reference, slot, _⟩ := homes.word_at _ _ specified
        exact ⟨reference, slot⟩)
      left right output borrowHome (scalarBorrowValue original left right) _
      (by simp [scalarBorrowValue]) call
      (call.after_memory_below preserved localFormed
        (write_preserves_static_world _ _ _ _ _ _ beforeCall.2 localWrite))
      preserved homes.writable enteredWF authority borrowSlot cleared
  have first := scalar_indexed_borrow contract 0 (binaryArguments left right output) frame
    storedLocal (inputLimb original left 0) (inputLimb original right 0) _ borrowHome (results 0)
    state.call.1.1 state.flagBound state.flagRead state.flagWrite (state.resultWrites 0)
    (Or.inl (Ne.symm (state.flagSeparate 0))) post
    (fun after formed world framed math =>
      scalar_borrow_run_next contract 0 (state.advance 0 math formed world framed) post
        fun _ second => scalar_borrow_run_next contract 1 second post
          fun _ third => scalar_borrow_run_next contract 2 third post
            (continuation borrowHome results))
  conv at first in (scalarBorrowCall _) => cbv
  cil_contract_steps [found, state.flagSlot, state.resultSlots 0, localAddress,
    access_reference_valid _ _ _ _ _ state.flagWrite,
    access_reference_valid _ _ _ _ _ (state.resultWrites 0)] until first

end UInt256Proof.Subtract.Safety