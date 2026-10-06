import UInt256.Methods.Add.SSEScalarResult
import UInt256.Methods.Add.ScalarSmallFacts

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- Both checked operand prefixes lead to the certified SSE route when neither
    initial operand fits in one limb. No caller separation is required. -/
theorem sse_scalar_large_entry (original entered : CIL.Safety.Memory)
    (left right output : Reference) (flag : BitVec 32) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody
      (binaryArguments left right output ++ [.scalar (.i32 flag)]) original = .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (largeRight : inputLimb original right 1 ||| inputLimb original right 2 |||
      inputLimb original right 3 ≠ BitVec.ofNat 64 0)
    (largeLeft : inputLimb original left 1 ||| inputLimb original left 2 |||
      inputLimb original left 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 0
        (binaryArguments left right output ++ [.scalar (.i32 flag)]) frame [] entered =
          .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let args := binaryArguments left right output ++ [.scalar (.i32 flag)]
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply scalar_right_prefix_checked original entered left right output [.scalar (.i32 flag)]
    frame call setup homes post
  intro rightHome before rightSlot rightRead preserved beforeCall authority
  apply scalar_left_prefix_checked original entered before left right output rightHome [.scalar (.i32 flag)]
    frame call enteredWF homes beforeCall preserved authority rightSlot rightRead largeRight post
  intro leftHome current ready
  have specified : scalarLocalSpecs[0]? = some (some 0) := by simp [scalarLocalSpecs, cil_code]
  obtain ⟨reference, _, fresh, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨allocation, present⟩ := access_requirements writable
  have currentWrite := ready.authority.access writable (enteredWF.1 _ _ present.present).1
  obtain ⟨currentAllocation, currentPresent⟩ := access_requirements currentWrite
  have next := Nat.le_trans fresh (Nat.le_of_lt (ready.call.1.1.1 _ _ currentPresent.present).1)
  have finish := sse_scalar_vector_finish original current frame left right output flag call ready.call
    ready.preserved next (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1)
  change ∃ fuel final returned,
    run Extracted.program fuel Extracted.addScalarIndex 69 args frame
      [.scalar (.i64 (inputLimb original left 1 ||| inputLimb original left 2 ||| inputLimb original left 3))]
      current = .ok (final, returned) ∧ post final returned
  apply run_next_exists post (show Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody by rfl)
    (by rfl)
  · simp [step, checkedValue, numericValue, largeLeft, pureArity, scalars, CIL.step, CIL.truth,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exact finish

#print axioms sse_scalar_large_entry

private theorem reporting_result {original final : CIL.Safety.Memory} {returned : List Value}
    {left right output : Reference} (flag : BitVec 32)
    (result : AddResult original final returned left right output) :
    ARMScalarReportingPost original final returned left right output flag :=
  ⟨⟨result.wellFormed, result.value, ⟨_, result.flag⟩, result.writable, result.footprint⟩,
    fun _ => result.flag⟩

/-- Complete SSE dispatcher execution, including both small-operand routes. -/
theorem sse_scalar_entry (original entered : CIL.Safety.Memory)
    (left right output : Reference) (flag : BitVec 32) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody
      (binaryArguments left right output ++ [.scalar (.i32 flag)]) original = .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 0
        (binaryArguments left right output ++ [.scalar (.i32 flag)]) frame [] entered =
          .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  by_cases rightSmall : inputLimb original right 1 ||| inputLimb original right 2 |||
      inputLimb original right 3 = BitVec.ofNat 64 0
  · apply scalar_right_prefix_checked original entered left right output [.scalar (.i32 flag)]
      frame call setup homes post
    intro home current slot loaded preserved currentCall authority
    rw [rightSmall]
    apply scalar_small_prefix false left right output home (inputLimb original right 0) frame current
      (currentCall.input_formed (by simp [scalarSmallSource])) (currentCall.output_formed (by simp)) slot loaded post
    have next := scalar_private_next original entered current frame homes enteredWF currentCall.1.1 authority
    have math := scalar_small_values false original current left right output call preserved rightSmall
    obtain ⟨fuel, final, values, executed, result⟩ := scalar_small_finish false original entered current frame
      left right output (inputLimb original right 0) call setup currentCall preserved next math.1 math.2
    exact ⟨fuel, final, values, executed, reporting_result flag result⟩
  · by_cases leftSmall : inputLimb original left 1 ||| inputLimb original left 2 |||
        inputLimb original left 3 = BitVec.ofNat 64 0
    · apply scalar_right_prefix_checked original entered left right output [.scalar (.i32 flag)]
        frame call setup homes post
      intro rightHome before rightSlot rightRead preserved beforeCall authority
      apply scalar_left_prefix_checked original entered before left right output rightHome [.scalar (.i32 flag)]
        frame call enteredWF homes beforeCall preserved authority rightSlot rightRead rightSmall post
      intro leftHome current ready
      rw [leftSmall]
      apply scalar_small_prefix true left right output leftHome (inputLimb original left 0) frame current
        (ready.call.input_formed (by simp [scalarSmallSource])) (ready.call.output_formed (by simp))
        ready.leftSlot ready.leftRead post
      have next := scalar_private_next original entered current frame homes enteredWF ready.call.1.1 ready.authority
      have math := scalar_small_values true original current left right output call ready.preserved leftSmall
      obtain ⟨fuel, final, values, executed, result⟩ := scalar_small_finish true original entered current frame
        left right output (inputLimb original left 0) call setup ready.call ready.preserved next math.1 math.2
      exact ⟨fuel, final, values, executed, reporting_result flag result⟩
    · exact sse_scalar_large_entry original entered left right output flag frame call setup homes rightSmall leftSmall

#print axioms sse_scalar_entry

end UInt256Proof.Add.Safety
