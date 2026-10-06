import UInt256.Methods.Add.ARMSmallEntry
import CIL.Safety.ReturnArity

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Ordinary valid caller views establish a checked invocation, including every
    visited running/returned state and the independent arithmetic/overflow result. -/
theorem checked_arm_small_contract (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ fuel final returned,
      InvocationCertificate Extracted.program Extracted.addScalarUInt64Index
        (armSmallArguments input output word) memory fuel final returned ∧
      ARMSmallPost memory final returned input output word := by
  let args := armSmallArguments input output word
  obtain ⟨frame, entered, setup, homes, _, _⟩ := arm_small_frame_setup memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    arm_small_entry enabled memory entered input output word frame call setup homes
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, armSmallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation Extracted.program Extracted.addScalarUInt64Index Extracted.addScalarUInt64Body
      args memory frame entered fuel final returned (by rfl) checked setup live executed, result⟩

#print axioms checked_arm_small_contract
end UInt256Proof.Add.Safety
