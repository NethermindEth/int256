import UInt256.Methods.Shift.ScalarExecution
import UInt256.Safety.ShiftContract

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
  (store : StoreLimbsContract program storage)
include bodyFound store
/-- Full checked invocation of the extracted numeric shift body, with the
    independent signed-count result and arbitrary valid caller overlap. -/
theorem scalar_correctness (memory : Memory) (input : Reference) (count : BitVec 32) (output : Reference)
    (call : CallingConditions program memory [input] [output]) :
    ShiftInvocation direction program index memory input count output := by
  have checked : (shiftArguments input count output).mapM (checkedValue memory) =
      .ok (shiftArguments input count output) := by
    have fi := call.input_formed (by simp : input ∈ [input])
    have fo := call.output_formed (by simp : output ∈ [output])
    simp [shiftArguments, checkedValue, numericValue, formValue, checkedAt, fi, fo,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨frame, entered, setup, homes, preserved, wf⟩ :=
    scalar_frame_setup profile direction storage memory (shiftArguments input count output) call.1.1
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  obtain ⟨fuel, final, returned, executed, empty, finalWF, value, writable, readable, footprint⟩ :=
    shift_body bodyFound store memory entered entered input output count frame (shiftArguments input count output)
      rfl rfl rfl call (call.after_frame_setup setup) preserved wf homes
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow
      (fun id member => (fresh.2 id member).1)
  subst returned
  exact ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ bodyFound checked setup live executed,
    value, writable, readable, footprint⟩


#print axioms scalar_correctness
end UInt256Proof.Shift.Safety
