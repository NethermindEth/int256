import UInt256.Methods.Add.ScalarLeftMemory
import UInt256.Methods.Add.ScalarCarryPrefix

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
