import UInt256.Methods.Add.ScalarSetup
import UInt256.Methods.Add.ScalarPrefix
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow
import CIL.Safety.LocalSnapshotSteps
import UInt256.Safety.InputWords

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- Discharge every prefix memory operation from ordinary calling conditions
    and actual frame setup. Only the branch continuation remains to be proved. -/
theorem scalar_right_prefix_checked (memory entered : CIL.Safety.Memory)
    (left right output : Reference) (extra : List Value) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (binaryArguments left right output ++ extra)
      memory = .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8) →
      MemoryBelow memory.nextIdentity memory after →
      CallingConditions Extracted.program after [left, right] [output] →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex scalarFirstDecision
          (binaryArguments left right output ++ extra) frame
          [.scalar (.i64 (inputLimb memory right 1 ||| inputLimb memory right 2 |||
            inputLimb memory right 3))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex 0
        (binaryArguments left right output ++ extra) frame [] entered = .ok (result, returned) ∧
      post result returned := by
  have enteredCall := call.after_frame_setup setup
  have valid := enteredCall.1
  have enteredFormed := valid.1
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have writable := homes.writable
  obtain ⟨home, slot, _, _, ready⟩ := homes.word_at 0 0 (by simp [scalarLocalSpecs, cil_code])
  have limbs := fun current below =>
    call.input_words_kept (current := current) below right (by simp)
  have done := fun after (written : write entered home
      (numberBytes (inputLimb memory right 0).toNat 8) 1 = .ok after) kept valid =>
    continuation home after slot (write_readback _ _ _ _ _ written) kept
      ⟨valid, write_preserves_static_world _ _ _ _ _ _ enteredCall.2 written⟩
  cil_contract_steps (snapshots := LocalSnapshots.empty entered frame.locals)
    [binaryArguments, slot, ready, limbs _ preserved, CIL.FeatureProfile.evaluate,
      BitVec.ofNat_eq_ofNat] until done _ localWrite preserved valid localAccess

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- The two saved low limbs refer to the initial caller bytes. Caller storage
    remains unchanged while all entered-frame homes retain access authority. -/
structure ScalarLowWords (memory entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output rightHome leftHome : Reference) : Prop where
  call : CallingConditions Extracted.program current [left, right] [output]
  preserved : MemoryBelow memory.nextIdentity memory current
  authority : AccessBelow entered.nextIdentity entered current
  rightSlot : frame.locals[0]? = some (.bytes .word64 rightHome)
  leftSlot : frame.locals[1]? = some (.bytes .word64 leftHome)
  rightRead : read current rightHome 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8)
  leftRead : read current leftHome 8 1 = .ok (numberBytes (inputLimb memory left 0).toNat 8)

theorem scalar_left_prefix_checked (memory entered before : CIL.Safety.Memory)
    (left right output rightHome : Reference) (extra : List Value) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (beforeCall : CallingConditions Extracted.program before [left, right] [output])
    (preserved : MemoryBelow memory.nextIdentity memory before)
    (authority : AccessBelow entered.nextIdentity entered before)
    (rightSlot : frame.locals[0]? = some (.bytes .word64 rightHome))
    (rightRead : read before rightHome 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8))
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ leftHome after,
      ScalarLowWords memory entered after frame left right output rightHome leftHome →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex scalarSecondDecision
          (binaryArguments left right output ++ extra) frame
          [.scalar (.i64 (inputLimb memory left 1 ||| inputLimb memory left 2 |||
            inputLimb memory left 3))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarFirstDecision
        (binaryArguments left right output ++ extra) frame
        [.scalar (.i64 (inputLimb memory right 1 ||| inputLimb memory right 2 |||
          inputLimb memory right 3))] before = .ok (result, returned) ∧ post result returned := by
  have valid := beforeCall.1
  have beforeFormed := valid.1
  have writable := homes.writable
  obtain ⟨leftHome, leftSlot, _, _, initialAccess⟩ :=
    homes.word_at 1 0 (by simp [scalarLocalSpecs, cil_code])
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ initialAccess
  have ready := authority.access initialAccess (enteredWF.1 _ _ present).1
  have limbs := fun current below =>
    call.input_words_kept (current := current) below left (by simp)
  conv in scalarFirstDecision => cbv
  have ordered := homes.ordered 0 1 rightHome leftHome (by decide) rightSlot leftSlot
  have done := fun after (written : write before leftHome
      (numberBytes (inputLimb memory left 0).toNat 8) 1 = .ok after) kept access valid =>
    continuation leftHome after
      ⟨⟨valid, write_preserves_static_world _ _ _ _ _ _ beforeCall.2 written⟩, kept, access,
        rightSlot, leftSlot, ((write_preserves_memory_below _ _ _ _ _ leftHome.allocation
          (Nat.le_refl _) written).read rightHome ordered 8 1).trans rightRead,
        write_readback _ _ _ _ _ written⟩
  cil_contract_steps (snapshots := LocalSnapshots.empty before frame.locals)
    [binaryArguments, largeRight, leftSlot, ready, limbs _ preserved, BitVec.ofNat_eq_ofNat]
    until done _ localWrite preserved authority valid
/-- The scalar helper's actual invocation arguments on the public scalar path. -/
def scalarArguments (left right output : Reference) : List Value :=
  binaryArguments left right output ++ [.scalar (.i32 0)]

/-- From a valid call, construct the frame and execute both operand prefixes.
    The remaining obligation starts at the left small-operand decision with
    both original low words saved and all caller storage still unchanged. -/
theorem scalar_large_right_prefix (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ frame entered rightHome leftHome after,
      enterFrame Extracted.addScalarBody (scalarArguments left right output) memory = .ok (frame, entered) →
      WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals →
      ScalarLowWords memory entered after frame left right output rightHome leftHome →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex scalarSecondDecision
          (scalarArguments left right output) frame
          [.scalar (.i64 (inputLimb memory left 1 ||| inputLimb memory left 2 |||
            inputLimb memory left 3))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨frame, entered, setup, homes, _, enteredWF⟩ :=
    scalar_frame_setup memory (scalarArguments left right output) call.1.1
  have executed := scalar_right_prefix_checked memory entered left right output [.scalar (.i32 0)]
    frame call setup homes post (by
      intro rightHome before rightSlot rightRead preserved beforeCall authority
      exact scalar_left_prefix_checked memory entered before left right output rightHome
        [.scalar (.i32 0)] frame call enteredWF homes beforeCall preserved authority rightSlot rightRead
        largeRight post (fun leftHome after ready => continuation frame entered rightHome leftHome after setup homes ready))
  obtain ⟨fuel, result, returned, finished, satisfied⟩ := executed
  have checked : (scalarArguments left right output).mapM (checkedValue memory) =
      .ok (scalarArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [scalarArguments, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, result, returned, ?_, satisfied⟩
  change run Extracted.program fuel Extracted.addScalarIndex 0
    (scalarArguments left right output) frame [] entered = .ok (result, returned) at finished
  simpa only [invoke, cil_code, checked, setup, Except.mapError, Bind.bind, Except.bind]
    using finished

end UInt256Proof.Safety
