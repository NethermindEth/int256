import UInt256.Methods.Shift.SafetyCount
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- The zero-output branch initializes all output bytes without requiring them
    to have been initialized before the call, including overlapping views. -/
theorem shift_zero_output (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes 0 32) →
      CallingConditions Extracted.program after inputs outputs →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = memory.cells id offset) →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc 16) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 14) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have length : (numberBytes 0 32).length = 32 := by simp [numberBytes]
  obtain ⟨after, written, afterCall, outside, loaded⟩ := call.write_output_slice member 0 (numberBytes 0 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written loaded
  have done := continuation after loaded afterCall outside
  have formed := call.output_formed member
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  iterate 2
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
        storeValue, referenceAt, written, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact done

#print axioms shift_zero_output

/-- The zero branch returns normally and retires only private frame storage. -/
theorem shift_zero_finish (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference) (boundary : Nat)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 14) args frame [] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧ read final output 32 1 = .ok (numberBytes 0 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  apply shift_zero_output memory inputs outputs frame args output call member argument
  intro after loaded afterCall outside
  have retired := leaveFrame_preserves_memory_below frame after boundary owned
  refine ⟨1, leaveFrame frame after, [], ?_, rfl,
    leaveFrame_preserves_wellFormed frame after afterCall.1.1,
    (retired.read output outputOld 32 1).trans loaded,
    (retired.access output outputOld 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩)), ?_⟩
  · have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
    have fetched : shiftBody.code[shiftPc 16]? = some .ret := by rfl
    have returns : shiftBody.returnsValue = false := by rfl
    simp [run, found, fetched, returns, step, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro id old offset untouched
    exact (retired.cells id old offset).trans (outside id offset untouched)

#print axioms shift_zero_finish
end UInt256Proof.Shift.Safety
