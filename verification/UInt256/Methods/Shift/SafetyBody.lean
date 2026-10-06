import UInt256.Methods.Shift.SafetyDispatch
import UInt256.Methods.Shift.SafetyCountMath
import UInt256.Methods.Shift.SafetyFinish
import UInt256.Methods.Shift.SafetyZero
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

def ShiftResult (original final : Memory) (returned : List Value)
    (input output : Reference) (count : BitVec 32) : Prop :=
  returned = [] ∧ final.WellFormed ∧
  inputValue final output = result shiftDirection (inputValue original input) count ∧
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

/-- Execute the complete body from a valid private frame. The result is stated
    on the initial caller operand, with the public full-signed-count semantics. -/
theorem shift_body (original entered current : Memory) (input output : Reference)
    (count : BitVec 32) (frame : Frame) (args : List Value)
    (inputArgument : args[0]? = some (.reference (.address input)))
    (countArgument : args[1]? = some (.scalar (.i32 count)))
    (outputArgument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions Extracted.program original [input] [output])
    (currentCall : CallingConditions Extracted.program current [input] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (allowed : InitializationAllowed input output) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex 0 args frame [] current = .ok (final, returned) ∧
      ShiftResult original final returned input output count := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  apply shift_count_dispatch original.nextIdentity entered current [input] [output] frame args count
    countArgument currentCall enteredWF homes authority
  · intro after large selected retained valid access next
    obtain ⟨fuel, final, returned, executed, empty, wf, loaded, writable, outside⟩ :=
      shift_zero_finish after [input] [output] frame args output original.nextIdentity valid
        (by simp) outputArgument outputOld owned
    refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, ⟨_, loaded⟩, ?_⟩
    · rw [zero_read_value final output loaded]
      simp only [result, shift_zero_count count large selected]
    · intro id old offset untouched
      exact (outside id old offset untouched).trans
        ((preserved.trans retained).cells id old offset)
  · intro whole wholeHome after small selected wholeSlot wholeRead retained valid access next
    apply shift_prepared original entered after [input] [output] input output frame args count whole wholeHome
      inputArgument countArgument outputArgument (by simp) allowed wholeSlot wholeRead call valid (by simp)
      (preserved.trans retained) enteredWF homes access
    intro maskHome complementHome ready maskSlot complementSlot wholeRead maskRead complementRead snapshots kept readyCall readyAccess readyNext
    let bounded : Fin 4 := ⟨whole.toNat, small⟩
    let references : Fin 4 → Reference := fun i => (snapshots i).choose
    have slots := fun i => (snapshots i).choose_spec.1
    have reads := fun i => (snapshots i).choose_spec.2
    obtain ⟨fuel, final, returned, executed, empty, wf, calculated, writable, readable, outside⟩ :=
      shift_nonzero_finish bounded ready frame [input] args output count wholeHome maskHome complementHome
        references (inputLimb original input) original.nextIdentity outputArgument readyCall
        wholeSlot maskSlot complementSlot wholeRead maskRead complementRead slots reads outputOld owned
    refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, readable, ?_⟩
    · rw [input_limbs_value] at calculated
      have selectedCount := shift_selected_count count whole small selected
      cases direction : shiftDirection <;>
        simpa only [result, selectedCount, shiftValue, direction] using calculated
    · intro id old offset untouched
      exact (outside id old offset untouched).trans
        ((kept id old offset untouched).trans ((preserved.trans retained).cells id old offset))

#print axioms shift_body
end UInt256Proof.Shift.Safety
