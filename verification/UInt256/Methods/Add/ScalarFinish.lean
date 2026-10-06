import UInt256.Methods.Add.ScalarCarryStart
import UInt256.Methods.Add.ScalarTail

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

structure ScalarResult (original final : CIL.Safety.Memory) (values : List Value)
    (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = scalarSumValue original left right
  flag : values = [.scalar (.i32 (scalarOverflowFlag (scalarCarryValue original left right 4)))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Finish the extracted general scalar path, preserving the private carry
    across output writes and the original caller footprint across teardown. -/
theorem scalar_finish (original entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (scalarArguments left right output) original = .ok (frame, entered))
    (state : ScalarCarryState original current frame left right output carryHome results 4) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
        (scalarArguments left right output) frame [] current = .ok (final, values) ∧
      ScalarResult original final values left right output := by
  let words := scalarSumWord original left right
  let post := fun final values => ScalarResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply scalar_store_prefix left right output [.scalar (.i32 0)] frame current results words
    formed state.resultSlots (fun i => state.completed i i.isLt) post
  apply run_store_limbs [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := Extracted.addScalarBody) (op := .call Extracted.storeLimbsIndex 5)
  · simp only [cil_code]
  · conv in scalarStoreCall => cbv
    simp only [cil_code]
  · unfold storageArguments
    repeat' (conv in storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, step, checkedValue, numericValue, formValue, formed,
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
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨Extracted.addScalarBody.code.length + 1, leaveFrame frame stored,
      [.scalar (.i32 (scalarOverflowFlag (scalarCarryValue original left right 4)))],
      scalar_return _ _ _ _ _ state.carrySlot carryRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, rfl, ?_, ?_⟩
    · simpa only [inputValue, bytes, scalarSumValue] using value
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms scalar_finish

theorem ScalarResult.modular_sum {original final : CIL.Safety.Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    inputValue final output = inputValue original left + inputValue original right :=
  result.value.trans (scalar_sum_value original left right)

/-- Complete finite checked execution on the both-large branch, including
    initial-input modular arithmetic, exact carry flag and caller footprint. -/
theorem scalar_general_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (largeLeft : inputLimb memory left 1 ||| inputLimb memory left 2 |||
      inputLimb memory left 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ ScalarResult memory final values left right output := by
  apply scalar_general_carries memory left right output call largeRight largeLeft
    (fun final values => ScalarResult memory final values left right output)
  intro frame entered carryHome results after setup state
  exact scalar_finish memory entered after frame left right output carryHome results call setup state

#print axioms ScalarResult.modular_sum
#print axioms scalar_general_checked

end UInt256Proof.Safety
