import UInt256.Methods.Add.ARMScalarEntry

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- Certify the complete ARM dispatcher and all visited states from ordinary
    caller views. The reporting mode binds the exact initial-input overflow bit. -/
theorem checked_arm_scalar_contract (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate Extracted.program Extracted.addScalarIndex
        (vector128Arguments left right output flag) memory fuel final returned ∧
      ARMScalarReportingPost memory final returned left right output flag := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, setup, homes, _, _⟩ := scalar_frame_setup memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    arm_scalar_entry enabled memory entered left right output flag frame call setup homes
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation Extracted.program Extracted.addScalarIndex Extracted.addScalarBody
      args memory frame entered fuel final returned (by rfl) checked setup live executed, result⟩

#print axioms checked_arm_scalar_contract
end UInt256Proof.Add.Safety
