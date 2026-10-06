import UInt256.Methods.Multiply.EntrySafetyInvoke
import UInt256.Safety.InitializedOutput
import UInt256.Safety.OutputEncoding

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_initialized_contract (word : WordContract) (top : FullTopContract) :
    InitializedBinaryContract (fun left right => left * right) Extracted.program multiplyIndex := by
  intro memory left right output call
  obtain ⟨fuel, final, invoked, result⟩ := multiply_invoke word top memory left right output call
  obtain ⟨frame, entered, setup, _, _, _⟩ := multiply_frame_setup memory left right output call
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have fl := call.input_formed (by simp : left ∈ [left, right])
  have fr := call.input_formed (by simp : right ∈ [left, right])
  have fo := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) =
      .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, checkedAt, fl, fr, fo,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := call.binary_entry_live setup
  have ran : run Extracted.program fuel multiplyIndex 0 (productArgs left right output) frame [] entered =
      .ok (final, []) := by
    simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using invoked
  exact ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live ran,
    output_encoded_read final output _ result.readable result.value, result.writable, result.footprint⟩

#print axioms multiply_initialized_contract
end UInt256Proof.Multiply.Safety
