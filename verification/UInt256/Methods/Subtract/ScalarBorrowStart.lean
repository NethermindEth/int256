import UInt256.Methods.Subtract.ScalarBorrowState
import UInt256.Safety.CallerSetup

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety

/-- Derive all result homes, freshness and separation from actual frame setup;
    no new separation restrictions are imposed on caller views. -/
theorem scalar_borrow_initial_state {original entered current : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference}
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (borrowSlot : frame.locals[1]? = some (.bytes .word64 borrowHome))
    (borrowWrite : access current borrowHome 8 1 true = .ok ())
    (borrowRead : read current borrowHome 8 1 = .ok (numberBytes 0 8)) :
    ∃ results : Fin 4 → Reference, ScalarBorrowState original current frame left right output borrowHome results 0 := by
  have candidates : ∀ i : Fin 4, ∃ reference,
      frame.locals[i.val + 2]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧ access entered reference 8 1 true = .ok () := by
    intro i
    have specified : scalarLocalSpecs[i.val + 2]? = some (some 0) := by
      obtain ⟨i, bound⟩ := i
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨reference, slot, fresh, _, writable⟩ := homes.word_at (i.val + 2) 0 specified
    exact ⟨reference, slot, fresh, writable⟩
  let results : Fin 4 → Reference := fun i => Classical.choose (candidates i)
  have facts : ∀ i, frame.locals[i.val + 2]? = some (.bytes .word64 (results i)) ∧
      original.nextIdentity ≤ (results i).allocation ∧ access entered (results i) 8 1 true = .ok () :=
    fun i => Classical.choose_spec (candidates i)
  have borrowFresh := homes.word_bound 1 borrowHome borrowSlot
  refine ⟨results, ⟨currentCall, ?_, borrowSlot, fun i => (facts i).1,
    borrowWrite, ?_, borrowRead, by simp [scalarBorrowValue], ?_, ?_, ?_, borrowFresh,
    fun i => (facts i).2.1, preserved.cells, ?_⟩⟩
  · intro reference member
    exact call.input_bytes_of_memory_below preserved member
  · intro i
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (facts i).2.2
    exact authority.access (facts i).2.2 (enteredWF.1 _ _ present).1
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old borrowFresh),
      fun i => Nat.ne_of_lt (Nat.lt_of_lt_of_le old (facts i).2.1)⟩
  · intro i
    exact Ne.symm (Nat.ne_of_lt (homes.ordered 1 (i.val + 2) borrowHome (results i)
      (by omega) borrowSlot (facts i).1))
  · intro i j different
    have differentVal : i.val ≠ j.val := fun h => different (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne differentVal with before | after
    · exact Nat.ne_of_lt (homes.ordered (i.val + 2) (j.val + 2) (results i) (results j)
        (by omega) (facts i).1 (facts j).1)
    · exact Ne.symm (Nat.ne_of_lt (homes.ordered (j.val + 2) (i.val + 2) (results j) (results i)
        (by omega) (facts j).1 (facts i).1))
  · intro i impossible
    omega

#print axioms scalar_borrow_initial_state

end UInt256Proof.Subtract.Safety
