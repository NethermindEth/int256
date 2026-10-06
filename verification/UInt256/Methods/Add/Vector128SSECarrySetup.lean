import UInt256.Methods.Add.Vector128SSECarryState

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

/-- The five actual word homes are fresh and retain write authority through
    the checked vector prefix. Their contents need not all be initialized yet. -/
theorem vector128_sse_word_home (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) (index : Fin 5) :
    ∃ reference,
      slots[14 + index.val]? = some (.bytes .word64 reference) ∧
      frame.locals[15 + index.val]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧
      access current reference 8 1 true = .ok () := by
  have spec : vector128Specs[14 + index.val]? = some ⟨.word64, .i64 0, 0, rfl⟩ := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨reference, slot, fresh, _, writable⟩ := homes.home_at _ _ spec
  have actual : frame.locals[15 + index.val]? = some (.bytes .word64 reference) := by
    simpa [layout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using slot
  obtain ⟨allocation, ready⟩ := access_requirements writable
  exact ⟨reference, slot, actual, fresh, authority.access writable (enteredWF.1 _ _ ready.present).1⟩

/-- Build the full zero-carry invariant from actual homes and preserved caller
    memory. All separation obligations concern fresh private allocations. -/
theorem vector128_sse_carry_ready (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output carryHome : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (carryRead : read current carryHome 8 1 = .ok (numberBytes 0 8)) :
    ∃ results : Fin 4 → Reference,
      ScalarCarryState original current frame left right output carryHome results 0 15 16 := by
  classical
  have allHomes := vector128_sse_word_home original entered current frame root slots layout homes enteredWF authority
  obtain ⟨carry, carryLocal, actualCarry, carryFresh, carryWrite⟩ := allHomes 0
  have same : carry = carryHome := by simpa only [show 15 + (0 : Fin 5).val = 15 from rfl, carrySlot,
    Option.some.injEq, LocalSlot.bytes.injEq, true_and] using actualCarry.symm
  subst carry
  let results : Fin 4 → Reference := fun i => Classical.choose (allHomes ⟨i.val + 1, by omega⟩)
  have resultFacts (i : Fin 4) := Classical.choose_spec (allHomes ⟨i.val + 1, by omega⟩)
  have resultSlots (i : Fin 4) : slots[15 + i.val]? = some (.bytes .word64 (results i)) := by
    have found := (resultFacts i).1
    change slots[14 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  have ordered (i : Fin 4) : carryHome.allocation < (results i).allocation :=
    homes.ordered 14 (15 + i.val) .word64 .word64 carryHome (results i) (by omega) carryLocal (resultSlots i)
  refine ⟨results, currentCall, ?_, carrySlot, ?_, carryWrite, ?_, carryRead, by simp [scalarCarryValue],
    ?_, (fun i => Ne.symm (Nat.ne_of_lt (ordered i))), ?_, carryFresh, ?_, preserved.cells, ?_⟩
  · intro reference member
    exact call.input_bytes_of_memory_below preserved member
  · intro i
    have found := (resultFacts i).2.1
    change frame.locals[15 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  · intro i
    exact (resultFacts i).2.2.2
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old : reference.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old carryFresh),
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

/-- Start with the actual repair branch, initialize carry, and execute all four
    helper calls. The continuation receives complete initial-input result words. -/
theorem vector128_sse_repair_carry (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ carryHome results after,
      ScalarCarryState original after frame left right output carryHome results 4 15 16 →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 193 (binaryArguments left right output ++ extra)
          frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 162 (binaryArguments left right output ++ extra)
        frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_sse_repair_start (by rfl) original.nextIdentity entered current [left, right] [output]
    frame root slots layout (binaryArguments left right output ++ extra) currentCall enteredWF homes authority post
  intro carryHome after carrySlot carryRead retained afterCall afterAuthority _written
  obtain ⟨results, ready⟩ := vector128_sse_carry_ready original entered after frame root slots layout
    left right output carryHome call afterCall (preserved.trans retained) homes enteredWF afterAuthority carrySlot carryRead
  exact vector128_sse_carry_all ready extra post (continuation carryHome results)

#print axioms vector128_sse_repair_carry
#print axioms vector128_sse_word_home
#print axioms vector128_sse_carry_ready
end UInt256Proof.Add.Safety
