import UInt256.Methods.Subtract.ScalarBorrowPrefix
import UInt256.Methods.Subtract.BorrowArithmetic
import UInt256.Methods.Subtract.ScalarTail
import UInt256.Methods.Add.StorageCall
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety

/-- Finish the extracted general scalar path, preserving the private borrow
    across output writes and the original caller footprint across teardown. -/
theorem scalar_finish (original entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) original = .ok (frame, entered))
    (state : ScalarBorrowState original current frame left right output borrowHome results 4) :
    ∃ fuel final values,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
        (binaryArguments left right output) frame [] current = .ok (final, values) ∧
      ScalarResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => ScalarResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply scalar_store_prefix left right output frame current results words
    formed state.resultSlots (fun i => state.completed i i.isLt) post
  apply UInt256Proof.Safety.run_store_limbs [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := scalarBody) (op := .call Extracted.storeLimbsIndex 5)
  · rfl
  · rfl
  · unfold UInt256Proof.Safety.storageArguments
    repeat' (conv in UInt256Proof.Safety.storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, step, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact state.call
  · intro stored valid outside authority value
    obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have outputOld := (call.1.1.1 _ _ outputPresent).1
    obtain ⟨borrowAllocation, borrowPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.borrowWrite
    have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
    have distinct : borrowHome.allocation ≠ output.allocation :=
      Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.borrowFresh))
    have borrowRead := authority.read_eq state.borrowRead borrowOld
      (fun i _ => outside _ _ (Or.inl distinct))
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨scalarBody.code.length + 1, leaveFrame frame stored,
      [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))],
      scalar_return _ _ _ _ _ state.borrowSlot borrowRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, rfl, ?_, ?_⟩
    · simpa only [inputValue, bytes, scalarDifferenceValue] using value
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms scalar_finish

end UInt256Proof.Subtract.Safety
