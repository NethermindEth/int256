import UInt256.Methods.Add.VectorRepairExecution
import CIL.Safety.Certificate

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
open CIL.Vector UInt256Proof.SIMD

/-- Full checked invocation of the extracted repair helper, including its
    SkipInit entry and all visited-state reference/lifetime guarantees. -/
theorem checked_repair_contract (memory : Memory) (output : Reference)
    (sumValue generated propagation : BitVec 256)
    (call : CallingConditions Extracted.program memory [] [output]) :
    ∃ fuel final,
      InvocationCertificate Extracted.program repairIndex
        (repairArguments sumValue generated propagation output) memory fuel final
        [.scalar (.i32 (if (moveMask64 propagation + 2 * moveMask64 generated) &&& 16 > 0 then 1 else 0))] ∧
      read final output 32 1 = .ok (numberBytes
        (zip256 (· + ·) sumValue (cascadeVector (cascadeIndex (moveMask64 generated) (moveMask64 propagation)))).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let args := repairArguments sumValue generated propagation output
  obtain ⟨frame, entered, setup, homes, preserved, enteredWF⟩ := repair_frame_setup memory args call.1.1
  have enteredCall := call.after_frame_setup setup
  have authority : AccessBelow entered.nextIdentity entered entered :=
    ⟨fun _ _ => rfl, fun _ _ _ _ h => h, fun _ _ _ h => h⟩
  obtain ⟨fuel, final, executed, result, writable, footprint⟩ := repair_tail_execution memory entered entered
    [] [output] output frame args call enteredCall (by simp) setup enteredWF (Nat.le_refl _) homes authority
    rfl sumValue generated propagation rfl rfl rfl
  have formed := enteredCall.output_formed (reference := output) (by simp)
  have found : Extracted.program[repairIndex]? = some repairBody := by rfl
  have entry : run Extracted.program (fuel+2) repairIndex 0 args frame [] entered =
      .ok (final, [.scalar (.i32 (if (moveMask64 propagation + 2 * moveMask64 generated) &&& 16 > 0 then 1 else 0))]) := by
    apply Eq.trans
    · apply run_next found (by rfl)
      simp [step, args, repairArguments, checkedValue, formValue, formed, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply Eq.trans
    · apply run_next found (by rfl)
      simp [step, instruction, args, repairArguments, checkedValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact executed
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, repairArguments, checkedValue, numericValue, formValue, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have certificate := certify_invocation Extracted.program repairIndex repairBody args memory frame entered
    (fuel+2) final _ found checked setup live entry
  refine ⟨fuel+2, final, certificate, result, writable, ?_⟩
  intro id offset old outside
  exact (footprint id offset old outside).trans (preserved.cells id old offset)

#print axioms checked_repair_contract
end UInt256Proof.Add.Safety
