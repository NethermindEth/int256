import UInt256.Methods.Add.Vector128SSERepairRun
import UInt256.Methods.Add.Vector128FastEntry
import UInt256.Methods.Add.Vector128ReportingArithmetic
import CIL.Safety.ReturnArity

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

/-- Every route of the extracted SSE helper, with valid caller views and no
    separation restriction between its operands and output. -/
theorem checked_vector128_sse_contract (memory : CIL.Safety.Memory)
    (left right output : Reference) (flag : BitVec 32)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate Extracted.program vector128Index
        (binaryArguments left right output ++ [.scalar (.i32 flag)])
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      (flag ≠ BitVec.ofNat 32 0 → returned = addOverflow memory left right) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let args := binaryArguments left right output ++ [.scalar (.i32 flag)]
  obtain ⟨frame, entered, slots, setup, layout, homes, preserved, enteredWF⟩ :=
    vector128_frame_setup memory args call.1.1
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  by_cases fast : selectedPropagation128 flag (vector128BranchValue memory left right 11)
      (vector128BranchValue memory left right 12) = BitVec.ofNat 128 0
  · obtain ⟨fuel, final, returned, executed, scalar, result, writable, footprint⟩ :=
      vector128_fast_entry memory entered [left, right] [output] left right output frame slots args
        call setup layout homes (by simp) (by simp) (by simp) rfl rfl rfl flag rfl fast
    subst returned
    exact ⟨fuel, final, _,
      certify_invocation Extracted.program vector128Index vector128Body args memory frame entered
        fuel final _ (by rfl) checked setup live executed,
      result, fun reporting => vector128_snapshot_fast_flag memory left right flag reporting fast,
      writable, footprint⟩
  · obtain ⟨fuel, final, returned, executed, result⟩ :=
      vector128_sse_repair_entry memory entered left right output frame slots flag call setup layout homes fast
    rw [result.flag] at executed
    exact ⟨fuel, final, addOverflow memory left right,
      certify_invocation Extracted.program vector128Index vector128Body args memory frame entered
        fuel final _ (by rfl) checked setup live executed,
      result.value, fun _ => rfl, result.writable,
      fun id offset bound outside => result.footprint id bound offset outside⟩

#print axioms checked_vector128_sse_contract
end UInt256Proof.Add.Safety
