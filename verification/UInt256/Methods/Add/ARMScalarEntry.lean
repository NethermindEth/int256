import UInt256.Methods.Add.ARMScalarResult

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- Complete ARM scalar dispatcher execution, including both small-operand routes
    and the vector route. The initial operands may overlap output arbitrarily. -/
theorem arm_scalar_entry (enabled : Extracted.profile.advSimd = true)
    (original entered : Memory) (left right output : Reference) (flag : BitVec 32) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (vector128Arguments left right output flag) original =
      .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 0 (vector128Arguments left right output flag)
        frame [] entered = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let args := vector128Arguments left right output flag
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  have enteredCall := call.after_frame_setup setup
  have setupPreserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have enteredWF := enteredCall.1.1
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ source id, id ∈ (armScalarSavedFrame frame source).owned → original.nextIdentity ≤ id :=
    fun _ id member => (fresh.2 id member).1
  have rootSlot := (arm_scalar_slots enabled entered original.nextIdentity frame homes).1
  have root : ∀ source, (armScalarSavedFrame frame source).locals[7]? =
      some (.root (some (.address source))) := by
    intro source
    simp only [armScalarSavedFrame, List.getElem?_set_self', rootSlot]
    rfl
  have wordSlot : ∀ source home, frame.locals[8]? = some (.bytes .word64 home) →
      (armScalarSavedFrame frame source).locals[8]? = some (.bytes .word64 home) := by
    intro source home slot
    simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot
  apply arm_scalar_dispatch_prefix enabled original.nextIdentity entered [left, right] [output]
    frame args left right enteredCall enteredWF homes (by simp) (by simp) rfl rfl post
  intro home current slot loaded preserved currentCall authority
  have originalPreserved := setupPreserved.trans preserved
  have next := arm_scalar_watermark original entered current frame homes enteredWF currentCall.1.1 authority
  by_cases rightSmall : armScalarUpper current right = BitVec.ofNat 64 0
  · simp only [armScalarTarget, rightSmall, ite_true]
    have lowKept : inputLimb entered right 0 = inputLimb current right 0 := by
      simp only [inputLimb,
        call.input_bytes_of_memory_below setupPreserved (reference := right) (by simp),
        call.input_bytes_of_memory_below originalPreserved (reference := right) (by simp)]
    rw [lowKept] at loaded
    exact arm_scalar_small_finish enabled original current (armScalarSavedFrame frame left) args
      left right output left home (inputLimb current right 0) flag call
      (arm_scalar_select_input current [left, right] left output currentCall (by simp))
      originalPreserved next (owned left) (root left) (wordSlot left home slot) loaded rfl
      (arm_scalar_small_values false original current left right output call originalPreserved rightSmall).1
      (arm_scalar_small_values false original current left right output call originalPreserved rightSmall).2
  · by_cases leftSmall : armScalarUpper current left = BitVec.ofNat 64 0
    · simp only [armScalarTarget, rightSmall, leftSmall, ite_false, ite_true]
      apply arm_scalar_swap_prefix enabled original.nextIdentity entered current [left, right] [output]
        frame args left right currentCall enteredWF homes authority (by simp) (by simp) rfl rfl post
      intro swappedHome after swappedSlot swappedRead afterPreserved afterCall afterAuthority
      have allPreserved := originalPreserved.trans afterPreserved
      have afterNext := arm_scalar_watermark original entered after frame homes enteredWF afterCall.1.1 afterAuthority
      have rightKept : inputValue after right = inputValue current right := by
        simp only [inputValue,
          call.input_bytes_of_memory_below allPreserved (reference := right) (by simp),
          call.input_bytes_of_memory_below originalPreserved (reference := right) (by simp)]
      have sums := arm_scalar_small_values true original current left right output call originalPreserved leftSmall
      apply arm_scalar_small_finish enabled original after (armScalarSavedFrame frame right) args
        left right output right swappedHome (inputLimb current left 0) flag call
        (arm_scalar_select_input after [left, right] right output afterCall (by simp))
        allPreserved afterNext (owned right) (root right) (wordSlot right swappedHome swappedSlot) swappedRead rfl
      · simpa only [rightKept, ite_true] using sums.1
      · simpa only [rightKept, ite_true] using sums.2
    · simp only [armScalarTarget, rightSmall, leftSmall, ite_false]
      exact arm_scalar_vector_finish enabled original current (armScalarSavedFrame frame left)
        left right output flag call currentCall originalPreserved next (owned left)

#print axioms arm_scalar_entry
end UInt256Proof.Add.Safety
