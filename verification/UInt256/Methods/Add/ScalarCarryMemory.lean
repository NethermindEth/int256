import UInt256.Methods.Add.ScalarMemory
import UInt256.Methods.Add.ScalarCarryPrefix
import UInt256.Methods.Add.CarryState

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

structure ScalarCarryReady (memory entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output rightHome leftHome carryHome resultHome : Reference) : Prop where
  lowWords : ScalarLowWords memory entered current frame left right output rightHome leftHome
  carrySlot : frame.locals[2]? = some (.bytes .word64 carryHome)
  resultSlot : frame.locals[3]? = some (.bytes .word64 resultHome)
  carryRead : read current carryHome 8 1 = .ok (numberBytes 0 8)
  carryWrite : access current carryHome 8 1 true = .ok ()
  resultWrite : access current resultHome 8 1 true = .ok ()
  disjoint : WordsDisjoint carryHome resultHome

/-- Initialize carry in its private word home without disturbing either saved
    operand. All permissions come from actual frame setup and earlier writes. -/
theorem scalar_carry_store (memory entered before : CIL.Safety.Memory)
    (left right output rightHome leftHome : Reference) (args : List Value) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (lowWords : ScalarLowWords memory entered before frame left right output rightHome leftHome) :
    ∃ carryHome resultHome after,
      ScalarCarryReady memory entered after frame left right output rightHome leftHome carryHome resultHome ∧
      ∀ pc rest, step Extracted.addScalarBody (.setLocal 2) pc args frame
        (.scalar (.i64 0) :: rest) before = .ok (.next (pc + 1) rest frame after) := by
  have carrySpec : scalarLocalSpecs[2]? = some (some 0) := by simp [scalarLocalSpecs, cil_code]
  have resultSpec : scalarLocalSpecs[3]? = some (some 0) := by simp [scalarLocalSpecs, cil_code]
  obtain ⟨carryHome, carrySlot, fresh, _, initialCarry⟩ := homes.word_at 2 0 carrySpec
  obtain ⟨resultHome, resultSlot, _, _, initialResult⟩ := homes.word_at 3 0 resultSpec
  obtain ⟨carryAllocation, carryPresent, _, _⟩ := access_within_allocation _ _ _ _ _ initialCarry
  obtain ⟨resultAllocation, resultPresent, _, _⟩ := access_within_allocation _ _ _ _ _ initialResult
  have carryOld := (enteredWF.1 _ _ carryPresent).1
  have resultOld := (enteredWF.1 _ _ resultPresent).1
  have writable := lowWords.authority.access initialCarry carryOld
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 0 writable
  have authority := lowWords.authority.trans (write_preserves_access_below written _)
  have caller := lowWords.preserved.trans (write_preserves_memory_below _ _ _ _ _ _ fresh written)
  have afterCall := call.after_memory_below caller
    (write_preserves_wellFormed _ _ _ _ _ lowWords.call.1.1 written)
    (write_preserves_static_world _ _ _ _ _ _ lowWords.call.2 written)
  have earlier := write_preserves_memory_below _ _ _ _ _ carryHome.allocation (Nat.le_refl _) written
  have rightOrder := homes.ordered 0 2 rightHome carryHome (by decide) lowWords.rightSlot carrySlot
  have leftOrder := homes.ordered 1 2 leftHome carryHome (by decide) lowWords.leftSlot carrySlot
  have outputOrder := homes.ordered 2 3 carryHome resultHome (by decide) carrySlot resultSlot
  refine ⟨carryHome, resultHome, after,
    ⟨⟨afterCall, caller, authority, lowWords.rightSlot, lowWords.leftSlot,
      (earlier.read rightHome rightOrder 8 1).trans lowWords.rightRead,
      (earlier.read leftHome leftOrder 8 1).trans lowWords.leftRead⟩,
      carrySlot, resultSlot, loaded, authority.access initialCarry carryOld,
      authority.access initialResult resultOld, ?_⟩, ?_⟩
  · exact Or.inl (Nat.ne_of_lt outputOrder)
  · intro pc rest
    obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
      (body := Extracted.addScalarBody) (pc := pc) (args := args) (rest := rest) 0 carrySlot writable
    rw [written] at sameWrite
    cases sameWrite
    exact stepped

#print axioms scalar_carry_store

/-- Execute the both-large prefix and its first mathematical carry call from
    the state established by the two operand prefixes. -/
theorem scalar_first_carry_checked (memory entered before : CIL.Safety.Memory)
    (left right output rightHome leftHome : Reference) (args : List Value) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (lowWords : ScalarLowWords memory entered before frame left right output rightHome leftHome)
    (largeLeft : inputLimb memory left 1 ||| inputLimb memory left 2 |||
      inputLimb memory left 3 ≠ BitVec.ofNat 64 0)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ carryHome resultHome prepared after,
      ScalarCarryReady memory entered prepared frame left right output rightHome leftHome carryHome resultHome →
      CarryPost (inputLimb memory left 0) (inputLimb memory right 0) 0 carryHome resultHome prepared after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarFirstCarryCall + 1) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarSecondDecision args frame
        [.scalar (.i64 (inputLimb memory left 1 ||| inputLimb memory left 2 |||
          inputLimb memory left 3))] before = .ok (result, returned) ∧ post result returned := by
  obtain ⟨carryHome, resultHome, prepared, ready, stored⟩ := scalar_carry_store
    memory entered before left right output rightHome leftHome args frame call enteredWF homes lowWords
  apply scalar_carry_prefix args frame before prepared _ (inputLimb memory left 0)
    (inputLimb memory right 0) largeLeft leftHome rightHome carryHome resultHome
    ready.lowWords.leftSlot ready.lowWords.rightSlot ready.carrySlot ready.resultSlot
    ready.lowWords.leftRead ready.lowWords.rightRead
    (access_reference_valid _ _ _ _ _ ready.carryWrite)
    (access_reference_valid _ _ _ _ _ ready.resultWrite) stored post
  exact scalar_first_carry args frame prepared (inputLimb memory left 0) (inputLimb memory right 0)
    carryHome resultHome ready.lowWords.call.1.1 ready.carryRead ready.carryWrite ready.resultWrite
    ready.disjoint post (fun after math => continuation carryHome resultHome prepared after ready math)

#print axioms scalar_first_carry_checked

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem ScalarCarryState.run_next {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} (segment : Fin 3)
    (state : ScalarCarryState original before frame left right output carryHome results (segment.val + 1))
    (extra : List Value) (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results (segment.val + 2) →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall (segment.val + 1) + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall segment.val + 1)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  have slot : frame.locals[segment.val + 4]? = some (.bytes .word64 (results index)) := by
    simpa only [index, Nat.add_assoc] using state.resultSlots index
  apply scalar_carry_segment_checked segment left right output extra frame before
    (scalarCarryValue original left right (segment.val + 1)) carryHome (results index) state.call
    state.carrySlot slot state.carryBound state.carryRead state.carryWrite (state.resultWrites index)
    (Or.inl (Ne.symm (state.carrySeparate index))) post
  intro after math
  apply continuation after
  apply state.advance index
  simpa only [inputLimb, state.inputBytes left (by simp), state.inputBytes right (by simp)] using math

/-- Compose all three remaining extracted calls; the final continuation receives
    all four exact result words and the mathematical final carry. -/
theorem ScalarCarryState.run_remaining {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarCarryState original before frame left right output carryHome results 1)
    (extra : List Value) (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 0 + 1)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply state.run_next 0 extra post
  intro _ second
  apply second.run_next 1 extra post
  intro _ third
  exact third.run_next 2 extra post continuation

#print axioms ScalarCarryState.run_next
#print axioms ScalarCarryState.run_remaining

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- Derive all result homes, freshness and separation from actual frame setup;
    no new separation restrictions are imposed on caller views. -/
theorem ScalarCarryReady.initial_state {original entered current : CIL.Safety.Memory} {frame : Frame}
    {left right output rightHome leftHome carryHome resultHome : Reference}
    (ready : ScalarCarryReady original entered current frame left right output rightHome leftHome carryHome resultHome)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals) :
    ∃ results : Fin 4 → Reference, results 0 = resultHome ∧
      ScalarCarryState original current frame left right output carryHome results 0 := by
  have candidates : ∀ i : Fin 4, ∃ reference,
      frame.locals[i.val + 3]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧ access entered reference 8 1 true = .ok () := by
    intro i
    have specified : scalarLocalSpecs[i.val + 3]? = some (some 0) := by
      obtain ⟨i, bound⟩ := i
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> simp [scalarLocalSpecs, cil_code]
    obtain ⟨reference, slot, fresh, _, writable⟩ := homes.word_at (i.val + 3) 0 specified
    exact ⟨reference, slot, fresh, writable⟩
  let results : Fin 4 → Reference := fun i => Classical.choose (candidates i)
  have facts : ∀ i, frame.locals[i.val + 3]? = some (.bytes .word64 (results i)) ∧
      original.nextIdentity ≤ (results i).allocation ∧ access entered (results i) 8 1 true = .ok () :=
    fun i => Classical.choose_spec (candidates i)
  have carryFresh := homes.word_bound 2 carryHome ready.carrySlot
  have first : results 0 = resultHome := by
    have same := (facts 0).1
    rw [show (0 : Fin 4).val + 3 = 3 from rfl, ready.resultSlot] at same
    simpa using same.symm
  refine ⟨results, first, ⟨ready.lowWords.call, ?_, ready.carrySlot, fun i => (facts i).1,
    ready.carryWrite, ?_, ready.carryRead, by simp [scalarCarryValue], ?_, ?_, ?_, carryFresh,
    fun i => (facts i).2.1, ready.lowWords.preserved.cells, ?_⟩⟩
  · intro reference member
    exact call.input_bytes_of_memory_below ready.lowWords.preserved member
  · intro i
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (facts i).2.2
    exact ready.lowWords.authority.access (facts i).2.2 (enteredWF.1 _ _ present).1
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old carryFresh),
      fun i => Nat.ne_of_lt (Nat.lt_of_lt_of_le old (facts i).2.1)⟩
  · intro i
    exact Ne.symm (Nat.ne_of_lt (homes.ordered 2 (i.val + 3) carryHome (results i)
      (by omega) ready.carrySlot (facts i).1))
  · intro i j different
    have differentVal : i.val ≠ j.val := fun h => different (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne differentVal with before | after
    · exact Nat.ne_of_lt (homes.ordered (i.val + 3) (j.val + 3) (results i) (results j)
        (by omega) (facts i).1 (facts j).1)
    · exact Ne.symm (Nat.ne_of_lt (homes.ordered (j.val + 3) (i.val + 3) (results j) (results i)
        (by omega) (facts j).1 (facts i).1))
  · intro i impossible
    omega

#print axioms ScalarCarryReady.initial_state

/-- Execute the actual scalar invocation through all four carry calls on the
    both-large branch. Only final storage, flag production and return remain. -/
theorem scalar_general_carries (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (largeLeft : inputLimb memory left 1 ||| inputLimb memory left 2 |||
      inputLimb memory left 3 ≠ BitVec.ofNat 64 0)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ frame entered carryHome results after,
      enterFrame Extracted.addScalarBody (scalarArguments left right output) memory = .ok (frame, entered) →
      ScalarCarryState memory after frame left right output carryHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
          (scalarArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (result, returned) ∧ post result returned := by
  apply scalar_large_right_prefix memory left right output call largeRight post
  intro frame entered rightHome leftHome before setup homes lowWords
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply scalar_first_carry_checked memory entered before left right output rightHome leftHome
    (scalarArguments left right output) frame call enteredWF homes lowWords largeLeft post
  intro carryHome resultHome prepared after ready math
  obtain ⟨results, first, initial⟩ := ready.initial_state call enteredWF homes
  have math' : CarryPost (inputLimb memory left 0) (inputLimb memory right 0)
      (scalarCarryValue memory left right 0) carryHome (results 0) prepared after := by
    simpa only [scalarCarryValue, first] using math
  have firstDone := initial.advance 0 math'
  exact firstDone.run_remaining [.scalar (.i32 0)] post
    (fun final completed => continuation frame entered carryHome results final setup completed)

#print axioms scalar_general_carries

end UInt256Proof.Safety
