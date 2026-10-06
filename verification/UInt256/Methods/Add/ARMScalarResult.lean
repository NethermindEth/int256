import UInt256.Methods.Add.ARMScalarFacts
import UInt256.Methods.Add.ScalarReportingResult

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Complete the small route from its saved arguments, certified helper call,
    scalar forwarding return and parent retirement. -/
theorem arm_scalar_small_finish (enabled : Extracted.profile.advSimd = true)
    (original current : Memory) (frame : Frame) (args : List Value)
    (left right output source home : Reference) (word : BitVec 64) (flag : BitVec 32)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [source] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (root : frame.locals[7]? = some (.root (some (.address source))))
    (slot : frame.locals[8]? = some (.bytes .word64 home))
    (loaded : read current home 8 1 = .ok (numberBytes word.toNat 8))
    (outputArg : args[2]? = some (.reference (.address output)))
    (sum : inputValue current source + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right)
    (naturalSum : (inputValue current source).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 36 args frame [] current = .ok (final, returned) ∧
      ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  apply arm_scalar_small_arguments enabled current frame args source output home word root slot loaded
    (currentCall.input_formed (by simp)) outputArg (currentCall.output_formed (by simp)) post
  apply arm_small_parent_call enabled current source output word frame args currentCall post
  intro childFuel final returned certified result
  refine ⟨arm_scalar_retire original current final frame left right output returned call preserved next owned
    result.wellFormed (result.value.trans sum) ⟨_, result.flag⟩ result.writable result.footprint, ?_⟩
  intro _
  simpa only [naturalSum] using result.flag


/-- The vector route yields the same wrapping postcondition after parent retirement. -/
theorem arm_scalar_vector_finish (enabled : Extracted.profile.advSimd = true)
    (original current : Memory) (frame : Frame) (left right output : Reference) (flag : BitVec 32)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 25 (vector128Arguments left right output flag)
        frame [] current = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  apply vector128_arm_parent_call enabled current left right output flag frame currentCall post
  intro childFuel final returnedFlag certified result overflow writable footprint
  have wellFormed := invoke_preserves_wellFormed _ _ _ _ _ _ _ currentCall.1.1 certified.1
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  rw [keptLeft, keptRight] at result
  refine ⟨arm_scalar_retire original current final frame left right output [.scalar (.i32 returnedFlag)]
    call preserved next owned wellFormed result ⟨returnedFlag, rfl⟩ writable
    (fun id old offset untouched => footprint id offset old untouched), ?_⟩
  intro reporting
  have exactFlag := overflow reporting
  rw [keptLeft, keptRight] at exactFlag
  rw [exactFlag]

#print axioms arm_scalar_vector_finish

#print axioms arm_scalar_retire
#print axioms arm_scalar_small_finish
end UInt256Proof.Add.Safety
