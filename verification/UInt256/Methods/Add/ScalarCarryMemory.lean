import UInt256.Methods.Add.ScalarMemory
import UInt256.Methods.Add.ScalarCarryPrefix

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.Add.CarrySafety

/-- The carry word is initialized in its private home while caller storage is unchanged and
    every entered-frame home keeps its access. -/
structure ScalarCarryReady (memory entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome resultHome : Reference) : Prop where
  call : CallingConditions Extracted.program current [left, right] [output]
  preserved : MemoryBelow memory.nextIdentity memory current
  authority : AccessBelow entered.nextIdentity entered current
  carrySlot : frame.locals[2]? = some (.bytes .word64 carryHome)
  resultSlot : frame.locals[3]? = some (.bytes .word64 resultHome)
  carryRead : read current carryHome 8 1 = .ok (numberBytes 0 8)

/-- Execute the both-large prefix and its first mathematical carry call from
    the state established by the two operand prefixes. -/
theorem scalar_first_carry_checked (contract : CarryHelperContract Extracted.program Extracted.addWithCarryIndex) (memory entered before : CIL.Safety.Memory)
    (left right output rightHome leftHome : Reference) (args : List Value) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (lowWords : ScalarLowWords memory entered before frame left right output rightHome leftHome)
    (largeLeft : inputLimb memory left 1 ||| inputLimb memory left 2 |||
      inputLimb memory left 3 ≠ BitVec.ofNat 64 0)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ carryHome resultHome prepared after,
      ScalarCarryReady memory entered prepared frame left right output carryHome resultHome →
      after.WellFormed →
      (StaticWorldPreserved Extracted.program prepared after) →
      Confined [(carryHome, 8), (resultHome, 8)] prepared after →
      CarryPost (inputLimb memory left 0) (inputLimb memory right 0) 0 carryHome resultHome after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarFirstCarryCall + 1) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarSecondDecision args frame
        [.scalar (.i64 (inputLimb memory left 1 ||| inputLimb memory left 2 |||
          inputLimb memory left 3))] before = .ok (result, returned) ∧ post result returned := by
  obtain ⟨carryHome, carrySlot, _, _, initialCarry⟩ :=
    homes.word_at 2 0 (by simp [scalarLocalSpecs, cil_code])
  obtain ⟨resultHome, resultSlot, _, _, initialResult⟩ :=
    homes.word_at 3 0 (by simp [scalarLocalSpecs, cil_code])
  obtain ⟨_, carryPresent, _, _⟩ := access_within_allocation _ _ _ _ _ initialCarry
  obtain ⟨_, resultPresent, _, _⟩ := access_within_allocation _ _ _ _ _ initialResult
  have writable := homes.writable
  have valid := lowWords.call.1
  have beforeFormed := valid.1
  have preserved := lowWords.preserved
  have authority := lowWords.authority
  have snapshots := ((LocalSnapshots.empty before frame.locals).after_effect 0 .word64 rightHome
    (.i64 (inputLimb memory right 0)) _ lowWords.rightSlot rfl lowWords.rightRead
    (fun _ _ _ _ _ _ _ _ loaded => loaded)).after_effect 1 .word64 leftHome
    (.i64 (inputLimb memory left 0)) _ lowWords.leftSlot rfl lowWords.leftRead
    (fun _ _ _ _ _ _ _ _ loaded => loaded)
  conv in scalarSecondDecision => cbv
  cil_contract_steps (snapshots := snapshots)
    [largeLeft, authority.access initialCarry (enteredWF.1 _ _ carryPresent).1,
      BitVec.ofNat_eq_ofNat]
  have carryWrite := authority.access initialCarry (enteredWF.1 _ _ carryPresent).1
  have resultWrite := authority.access initialResult (enteredWF.1 _ _ resultPresent).1
  have carryRead : read storedLocal carryHome 8 1 = .ok (numberBytes 0 8) :=
    write_readback _ _ _ _ _ localWrite
  have done := scalar_indexed_carry contract 0 args frame storedLocal (inputLimb memory left 0)
    (inputLimb memory right 0) 0 carryHome resultHome localFormed (by decide) carryRead
    carryWrite resultWrite (Or.inl (Nat.ne_of_lt
      (homes.ordered 2 3 carryHome resultHome (by decide) carrySlot resultSlot))) post
    (continuation carryHome resultHome storedLocal ·
      ⟨⟨valid, write_preserves_static_world _ _ _ _ _ _ lowWords.call.2 localWrite⟩, preserved,
        authority, carrySlot, resultSlot, carryRead⟩)
  cil_contract_steps [carrySlot, resultSlot, access_reference_valid _ _ _ _ _ carryWrite,
    access_reference_valid _ _ _ _ _ resultWrite] until done
end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.Add.CarrySafety

theorem scalar_carry_run_next (contract : CarryHelperContract Extracted.program Extracted.addWithCarryIndex) {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} (segment : Fin 3)
    (state : ScalarCarryState (program := Extracted.program) original before frame left right output carryHome results (segment.val + 1))
    (extra : List Value) (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState (program := Extracted.program) original after frame left right output carryHome results (segment.val + 2) →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall (segment.val + 1) + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall segment.val + 1)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  have slot : frame.locals[segment.val + 4]? = some (.bytes .word64 (results index)) := by
    simpa only [index, Nat.add_assoc] using state.resultSlots index
  apply scalar_carry_segment_checked contract segment left right output extra frame before
    (scalarCarryValue original left right (segment.val + 1)) carryHome (results index) state.call
    state.flagSlot slot state.flagBound state.flagRead state.flagWrite (state.resultWrites index)
    (Or.inl (Ne.symm (state.flagSeparate index))) post
  intro after formed world framed math
  apply continuation after
  refine state.advance index ?_ formed world framed
  simpa only [inputLimb, state.inputBytes left (by simp), state.inputBytes right (by simp)] using math

/-- Compose all three remaining extracted calls; the final continuation receives
    all four exact result words and the mathematical final carry. -/
theorem scalar_carry_run_remaining (contract : CarryHelperContract Extracted.program Extracted.addWithCarryIndex) {original before : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarCarryState (program := Extracted.program) original before frame left right output carryHome results 1)
    (extra : List Value) (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState (program := Extracted.program) original after frame left right output carryHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 0 + 1)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply scalar_carry_run_next contract 0 state extra post
  intro _ second
  apply scalar_carry_run_next contract 1 second extra post
  intro _ third
  exact scalar_carry_run_next contract 2 third extra post continuation

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.Add.CarrySafety

/-- Derive all result homes, freshness and separation from actual frame setup;
    no new separation restrictions are imposed on caller views. -/
theorem ScalarCarryReady.initial_state {original entered current : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome resultHome : Reference}
    (ready : ScalarCarryReady original entered current frame left right output carryHome resultHome)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals) :
    ∃ results : Fin 4 → Reference, results 0 = resultHome ∧
      ScalarCarryState (program := Extracted.program) original current frame left right output carryHome results 0 := by
  obtain ⟨results, state⟩ := UInt256Proof.AddSubtract.Safety.RippleState.initial
    Extracted.program (wordKinds scalarLocalSpecs) 2 0 original entered current frame frame.locals
    (by intro index; rfl) (fun i => by
      have specified : scalarLocalSpecs[2 + i.val]? = some (some 0) := by
        obtain ⟨i, bound⟩ := i
        have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl <;> simp [scalarLocalSpecs, cil_code]
      obtain ⟨reference, slot, _⟩ := homes.word_at _ _ specified
      exact ⟨reference, slot⟩)
    left right output carryHome (scalarCarryValue original left right) _
    (by simp [scalarCarryValue]) call ready.call ready.preserved homes.writable
    enteredWF ready.authority ready.carrySlot ready.carryRead
  refine ⟨results, ?_, state⟩
  have first := state.resultSlots 0
  rw [show (0 : Fin 4).val + (2 + 0 + 1) = 3 from rfl, ready.resultSlot] at first
  simpa using first.symm
/-- Execute the actual scalar invocation through all four carry calls on the
    both-large branch. Only final storage, flag production and return remain. -/
theorem scalar_general_carries (contract : CarryHelperContract Extracted.program Extracted.addWithCarryIndex) (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (largeLeft : inputLimb memory left 1 ||| inputLimb memory left 2 |||
      inputLimb memory left 3 ≠ BitVec.ofNat 64 0)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ frame entered carryHome results after,
      enterFrame Extracted.addScalarBody (scalarArguments left right output) memory = .ok (frame, entered) →
      ScalarCarryState (program := Extracted.program) memory after frame left right output carryHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
          (scalarArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (result, returned) ∧ post result returned := by
  apply scalar_large_right_prefix memory left right output call largeRight post
  intro frame entered rightHome leftHome before setup homes lowWords
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply scalar_first_carry_checked contract memory entered before left right output rightHome leftHome
    (scalarArguments left right output) frame enteredWF homes lowWords largeLeft post
  intro carryHome resultHome prepared after ready formed world framed math
  obtain ⟨results, first, initial⟩ := ready.initial_state call enteredWF homes
  subst first
  have math' : CarryPost (inputLimb memory left 0) (inputLimb memory right 0)
      (scalarCarryValue memory left right 0) carryHome (results 0) after := by
    simpa only [scalarCarryValue] using math
  have firstDone := initial.advance 0 math' formed world framed
  exact scalar_carry_run_remaining contract firstDone [.scalar (.i32 0)] post
    (fun final completed => continuation frame entered carryHome results final setup completed)

end UInt256Proof.Safety
