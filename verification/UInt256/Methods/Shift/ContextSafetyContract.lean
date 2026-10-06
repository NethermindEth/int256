import UInt256.Methods.Shift.SafetyBody
import UInt256.Safety.ShiftContract
import CIL.StorageProfileCoverage

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Full checked invocation of the extracted numeric shift body, with the
    independent signed-count result and arbitrary valid caller overlap. -/
theorem checked_shift_context (memory : Memory) (input : Reference) (count : BitVec 32) (output : Reference)
    (call : CallingConditions Extracted.program memory [input] [output])
    (allowed : InitializationAllowed input output) :
    ShiftInvocation shiftDirection Extracted.program shiftIndex memory input count output := by
  have checked : (shiftArguments input count output).mapM (checkedValue memory) =
      .ok (shiftArguments input count output) := by
    have fi := call.input_formed (by simp : input ∈ [input])
    have fo := call.output_formed (by simp : output ∈ [output])
    simp [shiftArguments, checkedValue, numericValue, formValue, checkedAt, fi, fo,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨frame, entered, setup, homes, preserved, wf⟩ :=
    shift_frame_setup memory (shiftArguments input count output) call.1.1
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  obtain ⟨fuel, final, returned, executed, empty, finalWF, value, writable, readable, footprint⟩ :=
    shift_body memory entered entered input output count frame (shiftArguments input count output)
      rfl rfl rfl call (call.after_frame_setup setup) preserved wf homes
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow
      (fun id member => (fresh.2 id member).1) allowed
  subst returned
  exact ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ (by rfl) checked setup live executed,
    value, writable, readable, footprint⟩


#print axioms checked_shift_context
end UInt256Proof.Shift.Safety
