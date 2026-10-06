import UInt256.Methods.Subtract.ScalarSmallChecked
import UInt256.Safety.ReportingContract

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- The scalar fallback is the final call before return; the fetched target is
    checked below against the independently discovered scalar helper. -/
def dispatchCall : Nat := Extracted.subtractVector256Body.code.length - 2

theorem dispatch_prefix (left right output : Reference) (frame : Frame) (memory : CIL.Safety.Memory)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel Extracted.subtractVector256Index dispatchCall (binaryArguments left right output)
        frame [.reference (.address output), .reference (.address right),
          .reference (.address left)] memory = .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.subtractVector256Index 0 (binaryArguments left right output)
        frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  conv at continuation in dispatchCall => cbv
  repeat' first
    | exact continuation
    | (simp (config := { failIfUnchanged := false })
       apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp (config := { implicitDefEqProofs := false })
           [cil_code, binaryArguments, step, checkedValue, numericValue, formValue, fl, fr, fo,
             pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem dispatch_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : CIL.Safety.Memory) :
    run Extracted.program 1 Extracted.subtractVector256Index (dispatchCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have lookup : Extracted.program[Extracted.subtractVector256Index]? = some Extracted.subtractVector256Body := by simp only [cil_code]
  have returned : Extracted.subtractVector256Body.code[dispatchCall + 1]? = some .ret := by
    conv in dispatchCall => cbv
    simp only [Nat.reduceAdd, cil_code]
  have returns : Extracted.subtractVector256Body.returnsValue = true := by rfl
  simp [run, lookup, returned, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem dispatch_contract_of_scalar
    (scalarChecked : ∀ memory left right output,
      CallingConditions Extracted.program memory [left, right] [output] →
      ∃ fuel final values,
        invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
          .ok (final, values) ∧ SubtractResult memory final values left right output) : ReportingBinaryContract (· - ·)
    (fun left right => decide (left.toNat < right.toNat))
    Extracted.program Extracted.subtractVector256Index := by
  intro memory left right output call
  have fits : FrameSetupFits Extracted.subtractVector256Body (binaryArguments left right output) := by
    simp [cil_code, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, values, invoked, result⟩ := scalarChecked entered left right output enteredCall
  rw [result.flag] at invoked
  have found : Extracted.program[Extracted.subtractVector256Index]? = some Extracted.subtractVector256Body := by simp only [cil_code]
  have fetched : Extracted.subtractVector256Body.code[dispatchCall]? = some (.call scalarIndex 3) := by
    conv in dispatchCall => cbv
    simp only [cil_code]
    rfl
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := output) (by simp)
  have stepped : step Extracted.subtractVector256Body (.call scalarIndex 3) dispatchCall
      (binaryArguments left right output) frame
      [.reference (.address output), .reference (.address right), .reference (.address left)]
      entered = .ok (.call scalarIndex (binaryArguments left right output) [] entered) := by
    simp [step, binaryArguments, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, invoked⟩
    ⟨1, dispatch_return _ (subtractUnderflow entered left right) frame after⟩
  let post : CIL.Safety.Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame after ∧ values = [.scalar (.i32 (subtractUnderflow entered left right))]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    dispatch_prefix left right output frame entered enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have inputSame : ∀ reference ∈ [left, right], inputValue entered reference = inputValue memory reference := by
    intro reference member
    exact call.input_value_after_setup setup member
  have flagSame : subtractUnderflow entered left right = subtractUnderflow memory left right := by
    simp only [subtractUnderflow, inputSame left (by simp), inputSame right (by simp)]
  rw [flagSame] at finished
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, leaveFrame frame after, ?_, ?_, ?_, ?_⟩
  · simpa only [subtractUnderflow, decide_eq_true_eq] using
      certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished
  all_goals
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame after memory.nextIdentity
      (fun id member => (fresh.2 id member).1)
    have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed (by simp : output ∈ [output]))
    have old := (call.1.1.1 _ _ present).1
  · have bytes : (fun offset => ((leaveFrame frame after).cells output.allocation offset).bits) =
        (fun offset => (after.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation old offset]
    have math := result.value
    rw [inputSame left (by simp), inputSame right (by simp)] at math
    simpa only [inputValue, bytes] using math
  · exact (retained.access output old 32 1 true).trans result.writable
  · intro id bound offset outside
    exact (retained.cells id bound offset).trans
      ((result.footprint id (Nat.lt_of_lt_of_le bound fresh.1.next) offset outside).trans (before.cells id bound offset))

#print axioms dispatch_prefix
#print axioms dispatch_return
#print axioms dispatch_contract_of_scalar
end UInt256Proof.Subtract.Safety
