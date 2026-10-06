import UInt256.Methods.Add.ScalarMemory
import UInt256.Methods.Add.ScalarLeftPrefix

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

theorem scalar_left_store (memory entered before : CIL.Safety.Memory)
    (left right output rightHome : Reference) (args : List Value) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (beforeCall : CallingConditions Extracted.program before [left, right] [output])
    (preserved : MemoryBelow memory.nextIdentity memory before)
    (authority : AccessBelow entered.nextIdentity entered before)
    (rightSlot : frame.locals[0]? = some (.bytes .word64 rightHome))
    (rightRead : read before rightHome 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8)) :
    ∃ leftHome after,
      ScalarLowWords memory entered after frame left right output rightHome leftHome ∧
      ∀ pc rest, step Extracted.addScalarBody (.setLocal 1) pc args frame
        (.scalar (.i64 (inputLimb memory left 0)) :: rest) before =
          .ok (.next (pc + 1) rest frame after) := by
  have specified : scalarLocalSpecs[1]? = some (some 0) := by
    simp [scalarLocalSpecs, cil_code]
  obtain ⟨leftHome, leftSlot, fresh, _, initialAccess⟩ := homes.word_at 1 0 specified
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ initialAccess
  have writable := authority.access initialAccess (enteredWF.1 _ _ present).1
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 (inputLimb memory left 0) writable
  have caller := preserved.trans (write_preserves_memory_below _ _ _ _ _ _ fresh written)
  have afterCall := call.after_memory_below caller
    (write_preserves_wellFormed _ _ _ _ _ beforeCall.1.1 written)
    (write_preserves_static_world _ _ _ _ _ _ beforeCall.2 written)
  have ordered := homes.ordered 0 1 rightHome leftHome (by decide) rightSlot leftSlot
  have earlier := write_preserves_memory_below _ _ _ _ _ leftHome.allocation (Nat.le_refl _) written
  have rightRetained := (earlier.read rightHome ordered 8 1).trans rightRead
  refine ⟨leftHome, after,
    ⟨afterCall, caller, authority.trans (write_preserves_access_below written _),
      rightSlot, leftSlot, rightRetained, loaded⟩, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := Extracted.addScalarBody) (pc := pc) (args := args) (rest := rest)
    (inputLimb memory left 0) leftSlot writable
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

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
  obtain ⟨leftHome, after, ready, stored⟩ := scalar_left_store memory entered before left right output
    rightHome _ frame call enteredWF homes beforeCall preserved authority rightSlot rightRead
  apply scalar_left_prefix left right output extra _ largeRight (inputLimb memory left) frame before after
    (beforeCall.input_formed (by simp)) (ready.call.input_formed (by simp)) ?_ ?_ stored post
    (continuation leftHome after ready)
  · intro rest
    rw [beforeCall.input_field_instruction (by simp) 0 rest]
    simp only [inputLimb, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  · intro index rest
    rw [ready.call.input_field_instruction (by simp) index rest]
    simp only [inputLimb, call.input_bytes_of_memory_below ready.preserved (reference := left) (by simp)]

#print axioms scalar_left_store
#print axioms scalar_left_prefix_checked

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
  simp only [cil_code] at setup
  simpa only [invoke, cil_code, checked, setup, Except.mapError, Bind.bind, Except.bind]
    using finished

#print axioms scalar_large_right_prefix

end UInt256Proof.Safety
