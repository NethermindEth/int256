import CIL.Safety.Equations
import UInt256.Methods.Shift.ScalarPrepared
import CIL.Safety.ReturnMemory
namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
include bodyFound
/-- The zero-output branch initializes all output bytes without requiring them
    to have been initialized before the call, including overlapping views. -/
theorem shift_zero_output (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference)
    (call : CallingConditions program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes 0 32) →
      CallingConditions program after inputs outputs →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = memory.cells id offset) →
      ∃ fuel final returned,
        run program fuel index (16) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (14) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have length : (numberBytes 0 32).length = 32 := by simp [numberBytes]
  obtain ⟨after, written, afterCall, outside, loaded⟩ := call.write_output_slice member 0 (numberBytes 0 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written loaded
  have writtenZero : write memory output (List.replicate 32 0) 1 = .ok after := written
  have done := continuation after loaded afterCall outside
  have formed := call.output_formed member
  have found := bodyFound
  cil_contract_steps [argument, formed, writtenZero, formValue, instruction, ordinaryAccessAlignment,
    staticInstruction, memoryInstruction, storeValue, referenceAt] until done

#print axioms shift_zero_output

/-- The zero branch returns normally and retires only private frame storage. -/
theorem shift_zero_finish (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference) (boundary : Nat)
    (call : CallingConditions program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run program fuel index (14) args frame [] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧ read final output 32 1 = .ok (numberBytes 0 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  apply shift_zero_output bodyFound memory inputs outputs frame args output call member argument
  intro after loaded afterCall outside
  have retired := leaveFrame_preserves_memory_below frame after boundary owned
  refine ⟨1, leaveFrame frame after, [], ?_, rfl,
    leaveFrame_preserves_wellFormed frame after afterCall.1.1,
    (retired.read output outputOld 32 1).trans loaded,
    (retired.access output outputOld 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩)), ?_⟩
  · have found := bodyFound
    have fetched : (scalarBody profile direction storage).code[16]? = some .ret := by rfl
    have returns : (scalarBody profile direction storage).returnsValue = false := by rfl
    exact run_return found fetched (by rfl) (by rfl)
  · intro id old offset untouched
    exact (retired.cells id old offset).trans (outside id offset untouched)

#print axioms shift_zero_finish
end UInt256Proof.Shift.Safety
