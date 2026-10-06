import UInt256.Methods.Add.ScalarEntryExecution
import UInt256.Methods.Add.EntrySafetySetup
import UInt256.Safety.Contract
import UInt256.Safety.CallerSetup

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Public Add through its scalar dispatcher preserves checked execution, initial-input modular arithmetic,
    normal void return, writable output and all caller bytes outside output. -/
theorem add_contract_of_scalar
    (child : ∀ memory left right output,
      CallingConditions Extracted.program memory [left, right] [output] →
      ∃ fuel final returned,
        InvocationCertificate Extracted.program Extracted.addScalarIndex
          (binaryArguments left right output ++ [.scalar (.i32 0)]) memory fuel final returned ∧
        ARMScalarReportingPost memory final returned left right output 0) :
    WrappingBinaryContract (· + ·) Extracted.program Extracted.entryIndex := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := UInt256Proof.Safety.checked_entry_setup memory left right output call
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [] ∧
    inputValue final output = inputValue memory left + inputValue memory right ∧
    access final output 32 1 true = .ok () ∧
    ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = memory.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel Extracted.entryIndex 0 (binaryArguments left right output)
        frame [] entered = .ok (final, returned) ∧ post final returned := by
    apply scalar_entry_dispatch child entered frame left right output enteredCall post
    intro childFuel final returned certified result
    have sum := result.value
    rw [call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])] at sum
    have retired := arm_scalar_retire memory entered final frame left right output returned
      call preserved fresh.1.next (fun id member => (fresh.2 id member).1)
      result.wellFormed sum result.scalar result.writable result.footprint
    exact ⟨rfl, retired.value, retired.writable, retired.footprint⟩
  obtain ⟨fuel, final, returned, executed, same, value, writable, footprint⟩ := finish
  subst returned
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have certified := certify_invocation Extracted.program Extracted.entryIndex Extracted.entryBody
    (binaryArguments left right output) memory frame entered fuel final []
    (by rfl) checked setup live executed
  exact ⟨fuel, final, certified, value, writable, footprint⟩

#print axioms add_contract_of_scalar
end UInt256Proof.Add.Safety
