import UInt256.Methods.Shift.ScalarFinish
import UInt256.Methods.Shift.ScalarZero
import UInt256.Methods.Shift.SafetyCountMath

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
  (store : StoreLimbsContract program storage)
def ShiftResult (original final : Memory) (returned : List Value)
    (input output : Reference) (count : BitVec 32) : Prop :=
  returned = [] ∧ final.WellFormed ∧
  inputValue final output = result direction (inputValue original input) count ∧
  access final output 32 1 true = .ok () ∧
  (∃ bytes, read final output 32 1 = .ok bytes) ∧
  (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset)

theorem zero_read_value (memory : Memory) (output : Reference)
    (loaded : read memory output 32 1 = .ok (numberBytes 0 32)) : inputValue memory output = 0 := by
  have decoded := congrArg CIL.Safety.byteNumber (read_result_snapshot loaded)
  rw [byteNumber_numberBytes, byteNumber_snapshot
    (fun offset => (memory.cells output.allocation offset).bits) output.offset 32] at decoded
  simp only [Nat.zero_mod] at decoded
  change BitVec.ofNat 256 (UInt256Model.byteNumber
    (fun offset => (memory.cells output.allocation offset).bits) output.offset 32) = _
  rw [← decoded]
  rfl

include bodyFound store

/-- Execute the complete body from its entered frame. The result is stated on the initial
    caller operand, with the public full-signed-count semantics. -/
theorem shift_body (original entered : Memory) (input output : Reference)
    (count : BitVec 32) (frame : Frame) (args : List Value)
    (inputArgument : args[0]? = some (.reference (.address input)))
    (countArgument : args[1]? = some (.scalar (.i32 count)))
    (outputArgument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (scalarBody profile direction storage) args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals) :
    ∃ fuel final returned,
      run program fuel index 0 args frame [] entered = .ok (final, returned) ∧
      ShiftResult (direction := direction) original final returned input output count := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id :=
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  apply shift_count_dispatch bodyFound original entered entered input output frame args count
    countArgument call homes.complete (VectorFrame.initial call setup)
  · intro after known large selected state
    obtain ⟨fuel, final, returned, executed, empty, wf, loaded, writable, outside⟩ :=
      shift_zero_finish bodyFound after [input] [output] frame args output original.nextIdentity
        state.call (by simp) outputArgument outputOld owned
    refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, ⟨_, loaded⟩, ?_⟩
    · rw [zero_read_value final output loaded]
      simp only [result, shift_zero_count count large selected]
    · intro id old offset untouched
      exact (outside id old offset untouched).trans (state.caller id old offset (Or.inl rfl))
  · intro whole after known small selected state wholeKnown
    apply shift_prepared bodyFound original entered after input output frame args count
      inputArgument countArgument call homes.complete known state
    intro ready state
    obtain ⟨fuel, final, returned, executed, empty, wf, calculated, writable, readable, outside⟩ :=
      shift_nonzero_finish bodyFound store ⟨whole.toNat, small⟩ original entered ready input
        output frame args count (inputLimb original input) known original.nextIdentity
        outputArgument state (by simpa using wholeKnown) outputOld owned
    refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, readable, ?_⟩
    · have model : UInt256Model.value (inputLimb original input) = inputValue original input :=
        UInt256Proof.input_value _ _
      rw [model] at calculated
      have selectedCount := shift_selected_count count whole small selected
      cases hdir : direction <;>
        simpa only [result, selectedCount, shiftValue, hdir] using calculated
    · intro id old offset untouched
      exact (outside id old offset untouched).trans (state.caller id old offset (Or.inl rfl))

end UInt256Proof.Shift.Safety
