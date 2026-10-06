import UInt256.Methods.Add.EntrySafetyExecution
import UInt256.Safety.Contract

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- The selected production entry, with both independent arithmetic and checked
    execution safety. This declaration is specific to the extracted profile. -/
theorem checked_add_contract : WrappingBinaryContract (· + ·) Extracted.program Extracted.entryIndex := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := checked_entry_setup memory left right output call
  obtain ⟨fuel, final, finished, result⟩ := entry_run_checked memory entered frame left right output call setup
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have lookup : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by
    simp only [cil_code]
  exact ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished,
    result.value, result.writable, result.footprint⟩

#print axioms checked_add_contract

end UInt256Proof.Safety
