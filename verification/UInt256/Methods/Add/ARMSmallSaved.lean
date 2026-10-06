import UInt256.Methods.Add.ARMSmallSetup

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armSmallWordSpec : NumericLocalSpec := ⟨.word64, .i64 0, 0, rfl⟩

theorem arm_small_input_spec (i : Fin 4) : armSmallSpecs[i.val]? = some armSmallWordSpec := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

structure ARMSmallSaved (original entered current : Memory)
    (input output : Reference) (frame : Frame) (done : Nat) : Prop where
  call : CallingConditions Extracted.program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  completed : ∀ i : Fin 4, i.val < done → ∃ reference,
    frame.locals[i.val]? = some (.bytes .word64 reference) ∧
      read current reference 8 1 = .ok (numberBytes (inputLimb original input i).toNat 8)

theorem ARMSmallSaved.save {original entered current : Memory}
    {input output : Reference} {frame : Frame}
    (index : Fin 4) (state : ARMSmallSaved original entered current input output frame index.val)
    (word : BitVec 64) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after, ARMSmallSaved original entered after input output frame (index.val + 1) ∧
      ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal index.val) pc
        (armSmallArguments input output word) frame
        (.scalar (.i64 (inputLimb original input index)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, authority, written, stepped⟩ :=
    arm_small_private_store original.nextIdentity entered current [input] [output] frame
      state.call enteredWF homes state.authority index.val armSmallWordSpec (arm_small_input_spec index)
      (.i64 (inputLimb original input index)) (inputLimb original input index).toNat rfl
  refine ⟨after, ⟨afterCall, state.preserved.trans preserved, authority, ?_⟩,
    fun pc rest => stepped pc _ rest⟩
  intro i saved
  by_cases equal : i = index
  · subst i
    exact ⟨reference, slot, loaded⟩
  · have earlier : i.val < index.val := by
      have different : i.val ≠ index.val := fun h => equal (Fin.ext h)
      omega
    obtain ⟨previous, previousSlot, previousRead⟩ := state.completed i earlier
    have different := Nat.ne_of_lt
      (homes.ordered i.val index.val .word64 .word64 previous reference earlier previousSlot slot)
    exact ⟨previous, previousSlot,
      write_preserves_disjoint_read written previousRead (Or.inl different)⟩

theorem arm_small_input_prefix_checked (enabled : Extracted.profile.advSimd = true) (original entered : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after, ARMSmallSaved original entered after input output frame 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 14
          (armSmallArguments input output word) frame [] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (armSmallArguments input output word) frame [] entered = .ok (result, returned) ∧
      post result returned := by
  have enteredCall := call.after_frame_setup setup
  have initial : ARMSmallSaved original entered entered input output frame 0 :=
    ⟨enteredCall, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow, by intro i impossible; omega⟩
  obtain ⟨first, saved1, step0⟩ := initial.save 0 word enteredCall.1.1 homes
  obtain ⟨second, saved2, step1⟩ := saved1.save 1 word enteredCall.1.1 homes
  obtain ⟨third, saved3, step2⟩ := saved2.save 2 word enteredCall.1.1 homes
  obtain ⟨fourth, saved4, step3⟩ := saved3.save 3 word enteredCall.1.1 homes
  let states : Nat → CIL.Safety.Memory := fun n => match n with
    | 0 => entered | 1 => first | 2 => second | 3 => third | _ => fourth
  have saved : ∀ i : Fin 4, ARMSmallSaved original entered (states i.val) input output frame i.val := by
    intro ⟨i, bound⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact initial
    · exact saved1
    · exact saved2
    · exact saved3
  apply arm_small_input_prefix enabled input output word (inputLimb original input) frame states
    (fun i => (saved i).call.input_formed (by simp)) ?_ ?_ post
    (continuation fourth saved4)
  · intro i rest
    rw [(saved i).call.input_field_instruction (by simp) i rest]
    simp only [inputLimb,
      call.input_bytes_of_memory_below (saved i).preserved (reference := input) (by simp)]
  · intro ⟨i, bound⟩ pc rest
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact step0 pc rest
    · exact step1 pc rest
    · exact step2 pc rest
    · exact step3 pc rest



/-- Later sum/flag homes cannot overwrite any of the four saved input limbs.
    Separation follows from actual ordered allocation, not a caller alias restriction. -/
theorem ARMSmallSaved.after_later_write {original entered current after : Memory}
    {input output : Reference} {frame : Frame} {done index : Nat}
    {kind : CIL.LocalKind} {reference : Reference} {bytes : List (BitVec 8)}
    (state : ARMSmallSaved original entered current input output frame done)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (later : 4 ≤ index) (slot : frame.locals[index]? = some (.bytes kind reference))
    (written : write current reference bytes 1 = .ok after)
    (preserved : MemoryBelow original.nextIdentity current after) :
    ARMSmallSaved original entered after input output frame done := by
  refine ⟨state.call.after_write written, state.preserved.trans preserved,
    state.authority.trans (write_preserves_access_below written _), ?_⟩
  intro i completed
  obtain ⟨home, homeSlot, loaded⟩ := state.completed i completed
  have separate := Nat.ne_of_lt
    (homes.ordered i.val index .word64 kind home reference (by omega) homeSlot slot)
  exact ⟨home, homeSlot, write_preserves_disjoint_read written loaded (Or.inl separate)⟩

#print axioms ARMSmallSaved.after_later_write

#print axioms arm_small_input_prefix_checked
#print axioms arm_small_input_spec
#print axioms ARMSmallSaved.save
end UInt256Proof.Add.Safety
