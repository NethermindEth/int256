import UInt256.Methods.Subtract.Vector128RepairRun
import UInt256.Methods.Subtract.Vector128FastEntry
import CIL.Safety.ReturnArity

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Every route of the extracted 128-bit helper preserves reference safety and
    proves the initial difference, exact underflow and arbitrary valid overlap. -/
theorem checked_vector128_contract (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      InvocationCertificate Extracted.program vector128Index (binaryArguments left right output)
        memory fuel final [.scalar (.i32 (subtractUnderflow memory left right))] ∧
      inputValue final output = inputValue memory left - inputValue memory right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let args := binaryArguments left right output
  obtain ⟨frame, entered, slots, setup, layout, homes, preserved, enteredWF⟩ :=
    vector128_frame_setup memory args call.1.1
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have routes : ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered = .ok (final, returned) ∧
      SubtractResult memory final returned left right output := by
    by_cases fast : vector128InitialPropagation memory left right = BitVec.ofNat 128 0
    · exact vector128_fast_entry memory entered left right output frame slots call setup layout homes fast
    · exact vector128_repair_entry memory entered left right output frame slots call setup layout homes fast
  obtain ⟨fuel, final, returned, executed, result⟩ := routes
  rw [result.flag] at executed
  exact ⟨fuel, final,
    certify_invocation Extracted.program vector128Index vector128Body args memory frame entered
      fuel final _ (by rfl) checked setup live executed,
    result.value, result.writable, fun id offset bound outside => result.footprint id bound offset outside⟩

#print axioms checked_vector128_contract
end UInt256Proof.Subtract.Safety
