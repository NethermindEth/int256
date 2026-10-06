import UInt256.Methods.Subtract.ScalarBorrowStart

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Initialize the private borrow word, retaining the saved right operand and
    deriving the complete chain invariant from actual allocated local homes. -/
theorem scalar_borrow_store (original entered before : CIL.Safety.Memory)
    (left right output rightHome : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (beforeCall : CallingConditions Extracted.program before [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original before)
    (authority : AccessBelow entered.nextIdentity entered before)
    (rightSlot : frame.locals[0]? = some (.bytes .word64 rightHome))
    (rightRead : read before rightHome 8 1 = .ok (numberBytes (inputLimb original right 0).toNat 8)) :
    ∃ borrowHome results after,
      ScalarBorrowState original after frame left right output borrowHome results 0 ∧
      read after rightHome 8 1 = .ok (numberBytes (inputLimb original right 0).toNat 8) ∧
      ∀ pc rest, step scalarBody (.setLocal 1) pc (binaryArguments left right output) frame
        (.scalar (.i64 0) :: rest) before = .ok (.next (pc + 1) rest frame after) := by
  have specified : scalarLocalSpecs[1]? = some (some 0) := by rfl
  obtain ⟨borrowHome, borrowSlot, fresh, _, initialWrite⟩ := homes.word_at 1 0 specified
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ initialWrite
  have old := (enteredWF.1 _ _ present).1
  have writable := authority.access initialWrite old
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 0 writable
  have afterAuthority := authority.trans (write_preserves_access_below written _)
  have caller := preserved.trans (write_preserves_memory_below _ _ _ _ _ _ fresh written)
  have afterCall := call.after_memory_below caller
    (write_preserves_wellFormed _ _ _ _ _ beforeCall.1.1 written)
    (write_preserves_static_world _ _ _ _ _ _ beforeCall.2 written)
  obtain ⟨results, state⟩ := scalar_borrow_initial_state call afterCall enteredWF homes caller
    afterAuthority borrowSlot (afterAuthority.access initialWrite old) loaded
  have earlier := write_preserves_memory_below _ _ _ _ _ borrowHome.allocation (Nat.le_refl _) written
  have rightOrder := homes.ordered 0 1 rightHome borrowHome (by decide) rightSlot borrowSlot
  refine ⟨borrowHome, results, after, state, (earlier.read rightHome rightOrder 8 1).trans rightRead, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := scalarBody) (pc := pc) (args := binaryArguments left right output) (rest := rest)
    0 borrowSlot writable
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

#print axioms scalar_borrow_store
end UInt256Proof.Subtract.Safety
