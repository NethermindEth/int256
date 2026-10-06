import UInt256.Methods.Subtract.BorrowState
import UInt256.Methods.Subtract.ScalarBorrowSegments
import UInt256.Safety.CallerSetup
import UInt256.Methods.Subtract.ScalarSafetyPrefix

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

theorem ScalarBorrowState.run_next {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} (segment : Fin 3)
    (state : ScalarBorrowState original before frame left right output borrowHome results (segment.val + 1))
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results (segment.val + 2) →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall (segment.val + 1) + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall segment.val + 1)
        (binaryArguments left right output) frame [] before = .ok (result, returned) ∧ post result returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  have slot : frame.locals[segment.val + 3]? = some (.bytes .word64 (results index)) := by
    simpa only [index, Nat.add_assoc] using state.resultSlots index
  apply scalar_borrow_segment_checked segment left right output frame before
    (scalarBorrowValue original left right (segment.val + 1)) borrowHome (results index) state.call
    state.borrowSlot slot state.borrowBound state.borrowRead state.borrowWrite (state.resultWrites index)
    (Or.inl (Ne.symm (state.borrowSeparate index))) post
  intro after math
  have leftSame : inputLimb before left index = inputLimb original left index := by
    simp only [inputLimb, state.inputBytes left (by simp)]
  have rightSame : inputLimb before right index = inputLimb original right index := by
    simp only [inputLimb, state.inputBytes right (by simp)]
  change BorrowPost (inputLimb before left index) (inputLimb before right index)
    (scalarBorrowValue original left right index.val) borrowHome (results index) before after at math
  rw [leftSame, rightSame] at math
  exact continuation after (state.advance index math)

/-- Compose all three remaining extracted calls; the final continuation receives
    all four exact result words and the mathematical final borrow. -/
theorem ScalarBorrowState.run_remaining {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarBorrowState original before frame left right output borrowHome results 1)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState original after frame left right output borrowHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 0 + 1)
        (binaryArguments left right output) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply state.run_next 0 post
  intro _ second
  apply second.run_next 1 post
  intro _ third
  exact third.run_next 2 post continuation

#print axioms ScalarBorrowState.run_next
#print axioms ScalarBorrowState.run_remaining

end UInt256Proof.Subtract.Safety

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

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Follow the extracted large-right branch and scalar feature guards through
    borrow initialization to the first discovered borrow call. -/
theorem scalar_borrow_prefix (left right output : Reference) (frame : Frame) (before after : Memory)
    (upper a b : BitVec 64) (large : upper ≠ BitVec.ofNat 64 0)
    (rightHome borrowHome resultHome : Reference)
    (leftFormed : form after left = .ok left)
    (leftRead : ∀ rest, instruction (.field 0) (.reference (.address left) :: rest) after =
      .ok (after, .scalar (.i64 a) :: rest))
    (rightSlot : frame.locals[0]? = some (.bytes .word64 rightHome))
    (borrowSlot : frame.locals[1]? = some (.bytes .word64 borrowHome))
    (resultSlot : frame.locals[2]? = some (.bytes .word64 resultHome))
    (rightRead : read after rightHome 8 1 = .ok (numberBytes b.toNat 8))
    (borrowFormed : form after borrowHome = .ok borrowHome)
    (resultFormed : form after resultHome = .ok resultHome)
    (stored : ∀ pc rest, step scalarBody (.setLocal 1) pc (binaryArguments left right output) frame
      (.scalar (.i64 0) :: rest) before = .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 0) (binaryArguments left right output) frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarFirstDecision (binaryArguments left right output) frame
        [.scalar (.i64 upper)] before = .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have adv : scalarBody.profile.advSimd = false := by rfl
  have sse : scalarBody.profile.sse42 = false := by rfl
  have rightLoaded := load_local_word64_of_read rightRead
  conv in scalarFirstDecision => cbv
  repeat' first
    | exact continuation
    | (simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat, large]
       apply run_next_exists post found (by rfl)
       first
       | exact stored _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, binaryArguments, checkedValue, numericValue, formValue, leftFormed,
             borrowFormed, resultFormed, rightSlot, borrowSlot, resultSlot, rightLoaded,
             leftRead, localAddress, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, adv, sse,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms scalar_borrow_prefix
/-- Execute the scalar body through its complete large-operand borrow chain.
    The continuation receives the four checked result words before output stores. -/
theorem scalar_general_borrows (original entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (large : inputLimb original right 1 ||| inputLimb original right 2 |||
      inputLimb original right 3 ≠ BitVec.ofNat 64 0)
    (post : Memory → List Value → Prop)
    (continuation : ∀ borrowHome results after,
      ScalarBorrowState original after frame left right output borrowHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply scalar_right_prefix_checked original entered left right output frame call setup homes post
  intro rightHome before rightSlot rightRead preserved beforeCall authority
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  obtain ⟨borrowHome, results, prepared, state, savedRight, stored⟩ := scalar_borrow_store
    original entered before left right output rightHome frame call beforeCall enteredWF homes
    preserved authority rightSlot rightRead
  have leftRead (rest : List Value) :
      instruction (.field 0) (.reference (.address left) :: rest) prepared =
        .ok (prepared, .scalar (.i64 (inputLimb original left 0)) :: rest) := by
    rw [state.call.input_field_instruction (by simp) 0 rest]
    simp only [inputLimb, state.inputBytes left (by simp)]
  apply scalar_borrow_prefix left right output frame before prepared _ (inputLimb original left 0)
    (inputLimb original right 0) large rightHome borrowHome (results 0)
    (state.call.input_formed (by simp)) leftRead rightSlot state.borrowSlot (state.resultSlots 0)
    savedRight (access_reference_valid _ _ _ _ _ state.borrowWrite)
    (access_reference_valid _ _ _ _ _ (state.resultWrites 0)) stored post
  apply scalar_indexed_borrow 0 (binaryArguments left right output) frame prepared
    (inputLimb original left 0) (inputLimb original right 0)
    (scalarBorrowValue original left right 0) borrowHome (results 0)
    state.call.1.1 state.borrowBound state.borrowRead state.borrowWrite (state.resultWrites 0)
    (Or.inl (Ne.symm (state.borrowSeparate 0))) post
  intro after math
  exact (state.advance 0 math).run_remaining post (fun final completed =>
    continuation borrowHome results final completed)

#print axioms scalar_general_borrows
end UInt256Proof.Subtract.Safety
