import UInt256.Methods.Add.ScalarCarryState
import UInt256.Methods.Add.ScalarCarryMemory

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
