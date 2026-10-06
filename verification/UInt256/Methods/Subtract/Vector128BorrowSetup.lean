import UInt256.Methods.Subtract.Vector128RepairStart
import UInt256.Methods.Subtract.BorrowCaller
import UInt256.Safety.LimbAccess
import UInt256.Methods.Subtract.BorrowState

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_borrow_segment (segment : Fin 4) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (a b : BitVec 64) (borrowHome resultHome : Reference)
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right)
    (leftRead : ∀ rest, instruction (.field segment)
      (.reference (.address left) :: rest) memory = .ok (memory, .scalar (.i64 a) :: rest))
    (rightRead : ∀ rest, instruction (.field segment)
      (.reference (.address right) :: rest) memory = .ok (memory, .scalar (.i64 b) :: rest))
    (borrowSlot : frame.locals[11]? = some (.bytes .word64 borrowHome))
    (resultSlot : frame.locals[segment.val + 12]? = some (.bytes .word64 resultHome))
    (borrowFormed : form memory borrowHome = .ok borrowHome)
    (resultFormed : form memory resultHome = .ok resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (86 + 7 * segment.val)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (80 + 7 * segment.val)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    dsimp at leftRead rightRead resultSlot
    first
    | change frame.locals[12]? = some (.bytes .word64 resultHome) at resultSlot
    | change frame.locals[13]? = some (.bytes .word64 resultHome) at resultSlot
    | change frame.locals[14]? = some (.bytes .word64 resultHome) at resultSlot
    | change frame.locals[15]? = some (.bytes .word64 resultHome) at resultSlot
    repeat'
      first
      | exact continuation
      | simp (config := { failIfUnchanged := false })
        apply run_next_exists post (by rfl : Extracted.program[vector128Index]? = some vector128Body) (by rfl)
        simp (config := { implicitDefEqProofs := false })
            [cil_code, step, checkedValue, formValue, leftFormed, rightFormed,
              borrowFormed, resultFormed, borrowSlot, resultSlot, localAddress, leftRead, rightRead,
              pureArity, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩


#print axioms vector128_borrow_segment
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_indexed_borrow (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (borrowHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, BorrowPost a b c borrowHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (87 + 7 * index.val) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (86 + 7 * index.val) args frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have borrowFormed := access_reference_valid _ _ _ _ _ borrowWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  apply run_borrow_call a b c borrowHome resultHome post (body := vector128Body)
    (op := .call Extracted.subtractWithBorrowIndex 4)
  · rfl
  · obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals rfl
  · simp [step, checkedValue, numericValue, formValue, borrowFormed, resultFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact wellFormed
  · exact incoming
  · exact borrowRead
  · exact borrowWrite
  · exact resultWrite
  · exact disjoint
  · simpa only [show 86 + 7 * index.val + 1 = 87 + 7 * index.val by omega] using continuation

#print axioms vector128_indexed_borrow

open UInt256Model.Safety

/-- Valid caller views discharge both field loads for each remaining limb;
    checked home accesses discharge address formation and the mathematical call. -/
theorem vector128_borrow_segment_checked (segment : Fin 4) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : CIL.Safety.Memory) (c : BitVec 64) (borrowHome resultHome : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (borrowSlot : frame.locals[11]? = some (.bytes .word64 borrowHome))
    (resultSlot : frame.locals[segment.val + 12]? = some (.bytes .word64 resultHome))
    (incoming : c.toNat ≤ 1)
    (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowHome resultHome)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      BorrowPost (inputLimb memory left segment)
        (inputLimb memory right segment) c borrowHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (87 + 7 * segment.val)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (80 + 7 * segment.val)
        (binaryArguments left right output ++ extra) frame [] memory = .ok (result, returned) ∧ post result returned := by
  apply vector128_borrow_segment segment left right output extra frame memory _ _ borrowHome resultHome
    (call.input_formed (by simp)) (call.input_formed (by simp))
    (fun rest => call.input_field_instruction (by simp) _ rest)
    (fun rest => call.input_field_instruction (by simp) _ rest) borrowSlot resultSlot
    (access_reference_valid _ _ _ _ _ borrowWrite) (access_reference_valid _ _ _ _ _ resultWrite) post
  exact vector128_indexed_borrow segment (binaryArguments left right output ++ extra)
    frame memory _ _ c borrowHome resultHome call.1.1 incoming borrowRead borrowWrite resultWrite disjoint post continuation

#print axioms vector128_borrow_segment_checked

end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Advance the shared borrow invariant through one actual vector repair call. -/
theorem vector128_borrow_next {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarBorrowState original before frame left right output borrowHome results index.val 11 12)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results (index.val + 1) 11 12 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (87 + 7 * index.val)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (80 + 7 * index.val)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_borrow_segment_checked index left right output extra frame before
    (scalarBorrowValue original left right index.val) borrowHome (results index) state.call
    state.borrowSlot (state.resultSlots index) state.borrowBound state.borrowRead state.borrowWrite
    (state.resultWrites index) (Or.inl (Ne.symm (state.borrowSeparate index))) post
  intro after math
  have leftSame : inputLimb before left index = inputLimb original left index := by
    simp only [inputLimb, state.inputBytes left (by simp)]
  have rightSame : inputLimb before right index = inputLimb original right index := by
    simp only [inputLimb, state.inputBytes right (by simp)]
  rw [leftSame, rightSame] at math
  exact continuation after (state.advance index math)

/-- All four borrow calls retain the initial operands, checked private homes and
    every completed result limb, even when caller input and output views overlap. -/
theorem vector128_borrow_all {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarBorrowState original before frame left right output borrowHome results 0 11 12)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results 4 11 12 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 108 (binaryArguments left right output ++ extra)
          frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 80 (binaryArguments left right output ++ extra)
        frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_borrow_next 0 state extra post
  intro _ first
  apply vector128_borrow_next 1 first extra post
  intro _ second
  apply vector128_borrow_next 2 second extra post
  intro _ third
  exact vector128_borrow_next 3 third extra post continuation

#print axioms vector128_borrow_next
#print axioms vector128_borrow_all
end UInt256Proof.Subtract.Safety

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
