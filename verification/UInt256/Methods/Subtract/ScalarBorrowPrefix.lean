import UInt256.Methods.Subtract.BorrowHelper
import UInt256.Methods.Subtract.ScalarBorrowSegments
import UInt256.Safety.CallerSetup
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
    dsimp at resultSlot leftRead rightRead tail
    simp (config := { failIfUnchanged := false }) only [CIL.fin_val_three, Nat.reduceMul]
      at leftRead rightRead tail
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
  intro rightHome before rightSlot rightRead preserved beforeCall authority _
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have specified : scalarLocalSpecs[1]? = some (some 0) := by rfl
  obtain ⟨borrowHome, borrowSlot, fresh, _, initialWrite⟩ := homes.word_at 1 0 specified
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ initialWrite
  have writable := authority.access initialWrite (enteredWF.1 _ _ present).1
  obtain ⟨prepared, written, _, loaded, _⟩ := store_local_word64 0 writable
  have caller := preserved.trans (write_preserves_memory_below _ _ _ _ _ _ fresh written)
  -- The chain invariant comes from the allocated homes; caller views need no separation.
  obtain ⟨results, state⟩ : ∃ results, ScalarBorrowState (program := Extracted.program) original
      prepared frame left right output borrowHome results 0 :=
    UInt256Proof.AddSubtract.Safety.RippleState.initial
      Extracted.program (wordKinds scalarLocalSpecs) 1 0 original entered prepared frame
      frame.locals (by intro index; rfl) (fun i => by
        have specified : scalarLocalSpecs[1 + i.val]? = some (some 0) := by
          obtain ⟨i, bound⟩ := i
          have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
          rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
        obtain ⟨reference, slot, _⟩ := homes.word_at _ _ specified
        exact ⟨reference, slot⟩)
      left right output borrowHome (scalarBorrowValue original left right) _
      (by simp [scalarBorrowValue]) call
      (call.after_memory_below caller (write_preserves_wellFormed _ _ _ _ _ beforeCall.1.1 written)
        (write_preserves_static_world _ _ _ _ _ _ beforeCall.2 written))
      caller homes.writable enteredWF (authority.trans (write_preserves_access_below written _))
      borrowSlot loaded
  have savedRight := ((write_preserves_memory_below _ _ _ _ _ borrowHome.allocation
    (Nat.le_refl _) written).read rightHome (homes.ordered 0 1 rightHome borrowHome (by decide)
      rightSlot borrowSlot) 8 1).trans rightRead
  have stored (pc : Nat) (rest : List Value) :
      step scalarBody (.setLocal 1) pc (binaryArguments left right output) frame
        (.scalar (.i64 0) :: rest) before = .ok (.next (pc + 1) rest frame prepared) := by
    obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
      (body := scalarBody) (pc := pc) (args := binaryArguments left right output) (rest := rest)
      0 borrowSlot writable
    rw [written] at sameWrite
    cases sameWrite
    exact stepped
  have leftRead (rest : List Value) :
      instruction (.fieldAt 0 8) (.reference (.address left) :: rest) prepared =
        .ok (prepared, .scalar (.i64 (inputLimb original left 0)) :: rest) := by
    have field := state.call.input_field_instruction (reference := left) (by simp) 0 rest
    simp only [Fin.val_zero, Nat.mul_zero] at field
    rw [field]
    simp only [inputLimb, state.inputBytes left (by simp)]
  have first := scalar_indexed_borrow contract 0 (binaryArguments left right output) frame
    prepared (inputLimb original left 0) (inputLimb original right 0) _ borrowHome (results 0)
    state.call.1.1 state.flagBound state.flagRead state.flagWrite (state.resultWrites 0)
    (Or.inl (Ne.symm (state.flagSeparate 0))) post
    (fun after formed world framed math =>
      scalar_borrow_run_next contract 0 (state.advance 0 math formed world framed) post
        fun _ second => scalar_borrow_run_next contract 1 second post
          fun _ third => scalar_borrow_run_next contract 2 third post
            (continuation borrowHome results))
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have adv : scalarBody.profile.advSimd = false := by rfl
  have sse : scalarBody.profile.sse42 = false := by rfl
  conv in scalarFirstDecision => cbv
  conv at first in (scalarBorrowCall _) => cbv
  cil_contract_steps [found, binaryArguments, large, adv, sse, stored, leftRead, rightSlot,
    state.flagSlot, state.resultSlots 0, load_local_word64_of_read savedRight, localAddress,
    state.call.input_formed (reference := left) (by simp),
    access_reference_valid _ _ _ _ _ state.flagWrite,
    access_reference_valid _ _ _ _ _ (state.resultWrites 0)] until first

end UInt256Proof.Subtract.Safety
