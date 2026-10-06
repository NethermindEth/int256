import UInt256.Methods.Add.VectorSafetyExecution
import CIL.Safety.Certificate

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def prepareArguments (left right output sum mask incoming propagation : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output),
    .reference (.address sum), .reference (.address mask), .reference (.address incoming),
    .reference (.address propagation)]

/-- Checked invocation of the extracted preparation helper. Its private-output
    separation is established by the parent frame, independently of execution.
    The caller still must perform the remaining carry repair for full addition. -/
theorem checked_prepare_contract (memory : Memory)
    (left right output sum mask incoming propagation : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output, sum, mask, incoming, propagation])
    (separate : PrepareSeparation output sum mask incoming propagation) :
    ∃ fuel final,
      InvocationCertificate Extracted.program vectorIndex
        (prepareArguments left right output sum mask incoming propagation) memory fuel final [] ∧
      PrepareResult final output sum mask incoming propagation (inputValue memory left) (inputValue memory right) ∧
      (∀ id offset, id < memory.nextIdentity →
        (∀ reference ∈ [output, sum, mask, incoming, propagation], OutsideOutput reference id offset) →
        final.cells id offset = memory.cells id offset) := by
  let args := prepareArguments left right output sum mask incoming propagation
  obtain ⟨frame, entered, setup, homes, _, _⟩ := vector_frame_setup memory args call.1.1
  obtain ⟨fuel, final, executed, result, footprint⟩ := vector_prepare_execution memory entered [left, right]
    [output, sum, mask, incoming, propagation] left right output sum mask incoming propagation frame args call setup homes
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) separate
    rfl rfl rfl rfl rfl rfl rfl
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    have fs := call.output_formed (reference := sum) (by simp)
    have fm := call.output_formed (reference := mask) (by simp)
    have fi := call.output_formed (reference := incoming) (by simp)
    have fp := call.output_formed (reference := propagation) (by simp)
    simp [args, prepareArguments, checkedValue, formValue, fl, fr, fo, fs, fm, fi, fp,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have certificate := certify_invocation Extracted.program vectorIndex vectorBody args memory frame entered
    fuel final [] (by rfl) checked setup live executed
  exact ⟨fuel, final, certificate, result, footprint⟩

#print axioms checked_prepare_contract
end UInt256Proof.Add.Safety
