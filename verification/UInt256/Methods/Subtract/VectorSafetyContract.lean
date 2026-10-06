import UInt256.Methods.Subtract.VectorSafetyExecution
import UInt256.Safety.ReportingContract
import CIL.Safety.ByteEncoding

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The selected extracted vector method satisfies the full reporting contract,
    including checked invocation, all visited states and retained output authority. -/
theorem checked_vector_contract : ReportingBinaryContract (· - ·)
    (fun a b => decide (a.toNat < b.toNat)) Extracted.program vectorIndex := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    vector_frame_setup memory (binaryArguments left right output) call.1.1
  obtain ⟨fuel, final, executed, loaded, writable, footprint⟩ :=
    vector_execution memory entered left right output frame call setup homes
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have certificate := certify_invocation Extracted.program vectorIndex vectorBody
    (binaryArguments left right output) memory frame entered fuel final _
    found checked setup (call.binary_entry_live setup) executed
  refine ⟨fuel, final, ?_, ?_, writable, ?_⟩
  · simpa only [decide_eq_true_eq] using certificate
  · have decoded := congrArg CIL.Safety.byteNumber (read_result_snapshot loaded)
    rw [byteNumber_numberBytes,
      byteNumber_snapshot (fun offset => (final.cells output.allocation offset).bits) output.offset 32] at decoded
    have bound : (inputValue memory left - inputValue memory right).toNat < 256^32 :=
      (inputValue memory left - inputValue memory right).isLt
    rw [Nat.mod_eq_of_lt bound] at decoded
    change BitVec.ofNat 256
      (UInt256Model.byteNumber (fun offset => (final.cells output.allocation offset).bits) output.offset 32) = _
    rw [← decoded, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro id old offset outside
    exact footprint id offset old outside

#print axioms checked_vector_contract
end UInt256Proof.Subtract.Safety
