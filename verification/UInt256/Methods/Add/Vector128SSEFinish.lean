import UInt256.Methods.Add.Vector128SSEOutput
import UInt256.Methods.Add.CarryArithmetic
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_sse_finish (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference) (extra : List Value)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarCarryState original current frame left right output carryHome results 4 15 16) :
    ∃ fuel final values,
      run Extracted.program fuel vector128Index 193
        (binaryArguments left right output ++ extra) frame [] current = .ok (final, values) ∧
      AddResult original final values left right output := by
  let words := scalarSumWord original left right
  let post := fun final values => AddResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply vector128_sse_store_prefix left right output extra frame current results words
    formed state.resultSlots (fun i => state.completed i i.isLt) post
  apply run_store_limbs [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := vector128Body) (op := .call Extracted.storeLimbsIndex 5)
  · rfl
  · rfl
  · unfold storageArguments
    repeat' (conv in storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, step, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact state.call
  · intro stored valid outside authority value
    obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have outputOld := (call.1.1.1 _ _ outputPresent).1
    obtain ⟨carryAllocation, carryPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.carryWrite
    have carryOld := (state.call.1.1.1 _ _ carryPresent).1
    have distinct : carryHome.allocation ≠ output.allocation :=
      Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.carryFresh))
    have carryRead := authority.read_eq state.carryRead carryOld
      (fun i _ => outside _ _ (Or.inl distinct))
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      owned
    refine ⟨5, leaveFrame frame stored,
      [.scalar (.i32 (scalarOverflowFlag (scalarCarryValue original left right 4)))],
      vector128_sse_return _ _ _ _ _ state.carrySlot carryRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
    · have computed : inputValue (leaveFrame frame stored) output = scalarSumValue original left right := by
        simpa only [inputValue, bytes, scalarSumValue] using value
      exact computed.trans (scalar_sum_value original left right)
    · rw [scalar_flag_overflow]
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms vector128_sse_finish
end UInt256Proof.Add.Safety
