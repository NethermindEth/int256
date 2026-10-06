import UInt256.Methods.Add.ARMSmallSaved

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

structure ARMSmallReady (original entered current : Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame) : Prop where
  saved : ARMSmallSaved original entered current input output frame 4
  sum : ∃ home, frame.locals[5]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes (inputLimb original input 0 + word).toNat 8)
  flag : ∃ home, frame.locals[6]? = some (.bytes .byte home) ∧
    read current home 1 1 = .ok (numberBytes 0 1)

/-- Derive both private stores and preserve all initial input snapshots before
    the first carry decision. No successful-store premise is left to the caller. -/
theorem arm_small_prepare (enabled : Extracted.profile.advSimd = true)
    (original entered current : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (saved : ARMSmallSaved original entered current input output frame 4)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, ARMSmallReady original entered after input output word frame →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 20
          (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 14
        (armSmallArguments input output word) frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨lowHome, lowSlot, lowRead⟩ := saved.completed 0 (by decide)
    obtain ⟨sumHome, middle, sumSlot, sumRead, sumPreserved, _, _, sumWritten, sumStep⟩ :=
      arm_small_private_store original.nextIdentity entered current [input] [output] frame
        saved.call enteredWF homes saved.authority 5 armSmallWordSpec (by rfl)
        (.i64 (inputLimb original input 0 + word)) (inputLimb original input 0 + word).toNat rfl
    have middleSaved := saved.after_later_write homes (by decide : 4 ≤ 5) sumSlot sumWritten sumPreserved
    obtain ⟨flagHome, after, flagSlot, flagRead, flagPreserved, _, _, flagWritten, flagStep⟩ :=
      arm_small_private_store original.nextIdentity entered middle [input] [output] frame
        middleSaved.call enteredWF homes middleSaved.authority 6 ⟨.byte, .i32 0, 0, rfl⟩ (by rfl)
        (.i32 0) 0 rfl
    have afterSaved := middleSaved.after_later_write homes (by decide : 4 ≤ 6) flagSlot flagWritten flagPreserved
    have separate := Nat.ne_of_lt
      (homes.ordered 5 6 .word64 .byte sumHome flagHome (by decide) sumSlot flagSlot)
    have sumAfter := write_preserves_disjoint_read flagWritten sumRead (Or.inl separate)
    have ready : ARMSmallReady original entered after input output word frame :=
      ⟨afterSaved, ⟨sumHome, sumSlot, sumAfter⟩, ⟨flagHome, flagSlot, flagRead⟩⟩
    apply arm_small_sum enabled input output lowHome word (inputLimb original input 0) frame
      current middle lowSlot lowRead (sumStep 17 _ []) post
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    apply run_next_exists post found (by rfl)
    · simp [step, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · exact run_next_exists post found (by rfl) (flagStep 19 _ []) (continuation after ready)

/-- Connect actual helper entry to a fully initialized carry-decision state. -/
theorem arm_small_ready_prefix (enabled : Extracted.profile.advSimd = true)
    (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, ARMSmallReady original entered after input output word frame →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 20
          (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (armSmallArguments input output word) frame [] entered = .ok (final, returned) ∧ post final returned := by
  apply arm_small_input_prefix_checked enabled original entered input output word frame call setup homes post
  intro current saved
  exact arm_small_prepare enabled original entered current input output word frame
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes saved post continuation

#print axioms arm_small_prepare
#print axioms arm_small_ready_prefix
end UInt256Proof.Add.Safety
