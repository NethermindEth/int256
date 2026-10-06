import UInt256.Methods.Subtract.Vector128BorrowState

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The five actual word homes are fresh and retain write authority through
    the checked vector prefix. Their contents need not all be initialized yet. -/
theorem vector128_word_home (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) (index : Fin 5) :
    ∃ reference,
      slots[10 + index.val]? = some (.bytes .word64 reference) ∧
      frame.locals[11 + index.val]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧
      access current reference 8 1 true = .ok () := by
  have spec : vector128Specs[10 + index.val]? = some ⟨.word64, .i64 0, 0, rfl⟩ := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨reference, slot, fresh, _, writable⟩ := homes.home_at _ _ spec
  have actual : frame.locals[11 + index.val]? = some (.bytes .word64 reference) := by
    simpa [layout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using slot
  obtain ⟨allocation, ready⟩ := access_requirements writable
  exact ⟨reference, slot, actual, fresh, authority.access writable (enteredWF.1 _ _ ready.present).1⟩

/-- Build the full zero-borrow invariant from actual homes and preserved caller
    memory. All separation obligations concern fresh private allocations. -/
theorem vector128_borrow_ready (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output borrowHome : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (borrowSlot : frame.locals[11]? = some (.bytes .word64 borrowHome))
    (borrowRead : read current borrowHome 8 1 = .ok (numberBytes 0 8)) :
    ∃ results : Fin 4 → Reference,
      ScalarBorrowState original current frame left right output borrowHome results 0 11 12 := by
  classical
  have allHomes := vector128_word_home original entered current frame root slots layout homes enteredWF authority
  obtain ⟨borrow, borrowLocal, actualBorrow, borrowFresh, borrowWrite⟩ := allHomes 0
  have same : borrow = borrowHome := by simpa only [show 11 + (0 : Fin 5).val = 11 from rfl, borrowSlot,
    Option.some.injEq, LocalSlot.bytes.injEq, true_and] using actualBorrow.symm
  subst borrow
  let results : Fin 4 → Reference := fun i => Classical.choose (allHomes ⟨i.val + 1, by omega⟩)
  have resultFacts (i : Fin 4) := Classical.choose_spec (allHomes ⟨i.val + 1, by omega⟩)
  have resultSlots (i : Fin 4) : slots[11 + i.val]? = some (.bytes .word64 (results i)) := by
    have found := (resultFacts i).1
    change slots[10 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  have ordered (i : Fin 4) : borrowHome.allocation < (results i).allocation :=
    homes.ordered 10 (11 + i.val) .word64 .word64 borrowHome (results i) (by omega) borrowLocal (resultSlots i)
  refine ⟨results, currentCall, ?_, borrowSlot, ?_, borrowWrite, ?_, borrowRead, by simp [scalarBorrowValue],
    ?_, (fun i => Ne.symm (Nat.ne_of_lt (ordered i))), ?_, borrowFresh, ?_, preserved.cells, ?_⟩
  · intro reference member
    exact call.input_bytes_of_memory_below preserved member
  · intro i
    have found := (resultFacts i).2.1
    change frame.locals[11 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  · intro i
    exact (resultFacts i).2.2.2
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old : reference.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old borrowFresh),
      fun i => Nat.ne_of_lt (Nat.lt_of_lt_of_le old (resultFacts i).2.2.1)⟩
  · intro i j different
    have distinct : i.val ≠ j.val := fun equal => different (Fin.ext equal)
    by_cases before : i.val < j.val
    · exact Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots i) (resultSlots j))
    · exact Ne.symm (Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots j) (resultSlots i)))
  · intro i
    exact (resultFacts i).2.2.1
  · intro i impossible
    omega

/-- Start with the actual repair branch, initialize borrow, and execute all four
    helper calls. The continuation receives complete initial-input result words. -/
theorem vector128_repair_borrow (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ borrowHome results after,
      ScalarBorrowState original after frame left right output borrowHome results 4 11 12 →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 108 (binaryArguments left right output ++ extra)
          frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 77 (binaryArguments left right output ++ extra)
        frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_repair_start original.nextIdentity entered current [left, right] [output]
    frame root slots layout (binaryArguments left right output ++ extra) currentCall enteredWF homes authority post
  intro borrowHome after borrowSlot borrowRead retained afterCall afterAuthority _written
  obtain ⟨results, ready⟩ := vector128_borrow_ready original entered after frame root slots layout
    left right output borrowHome call afterCall (preserved.trans retained) homes enteredWF afterAuthority borrowSlot borrowRead
  exact vector128_borrow_all ready extra post (continuation borrowHome results)

#print axioms vector128_repair_borrow
#print axioms vector128_word_home
#print axioms vector128_borrow_ready
end UInt256Proof.Subtract.Safety
