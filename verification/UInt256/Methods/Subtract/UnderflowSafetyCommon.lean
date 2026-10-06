import Extracted
import UInt256.Safety.CallerSetup
import CIL.Safety.StepComposition
import CIL.Safety.CallComposition
import CIL.Safety.ReturnMemory
import UInt256.Safety.ReportingContract

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Locate the public forwarding call immediately before its return. -/
def underflowCall : Nat := Extracted.entryBody.code.length - 2

theorem underflow_prefix (left right output : Reference) (frame : Frame) (memory : CIL.Safety.Memory)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex underflowCall (binaryArguments left right output)
        frame [.reference (.address output), .reference (.address right),
          .reference (.address left)] memory = .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex 0 (binaryArguments left right output)
        frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  conv at continuation in underflowCall => cbv
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

theorem underflow_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : CIL.Safety.Memory) :
    run Extracted.program 1 Extracted.entryIndex (underflowCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have lookup : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have returned : Extracted.entryBody.code[underflowCall + 1]? = some .ret := by
    conv in underflowCall => cbv
    simp only [Nat.reduceAdd, cil_code]
  have returns : Extracted.entryBody.returnsValue = true := by rfl
  simp [run, lookup, returned, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem underflow_contract_of_reporting
    (reporting : ReportingBinaryContract (· - ·)
      (fun a b => decide (a.toNat < b.toNat)) Extracted.program Extracted.subtractVector256Index) : ReportingBinaryContract (· - ·)
    (fun left right => decide (left.toNat < right.toNat))
    Extracted.program Extracted.entryIndex := by
  intro memory left right output call
  have fits : FrameSetupFits Extracted.entryBody (binaryArguments left right output) := by
    simp [cil_code, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, certificate, resultValue, resultWritable, resultFootprint⟩ :=
    reporting entered left right output enteredCall
  have invoked : invoke Extracted.program childFuel Extracted.subtractVector256Index
      (binaryArguments left right output) entered =
        .ok (after, [.scalar (.i32 ((if (inputValue entered left).toNat < (inputValue entered right).toNat then (1 : BitVec 32) else 0)))]) := by
    simpa only [decide_eq_true_eq] using certificate.1
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have fetched : Extracted.entryBody.code[underflowCall]? = some (.call Extracted.subtractVector256Index 3) := by
    conv in underflowCall => cbv
    simp only [cil_code]
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := output) (by simp)
  have stepped : step Extracted.entryBody (.call Extracted.subtractVector256Index 3) underflowCall
      (binaryArguments left right output) frame
      [.reference (.address output), .reference (.address right), .reference (.address left)]
      entered = .ok (.call Extracted.subtractVector256Index (binaryArguments left right output) [] entered) := by
    simp [step, binaryArguments, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, invoked⟩
    ⟨1, underflow_return _ ((if (inputValue entered left).toNat < (inputValue entered right).toNat then (1 : BitVec 32) else 0)) frame after⟩
  let post : CIL.Safety.Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame after ∧ values = [.scalar (.i32 ((if (inputValue entered left).toNat < (inputValue entered right).toNat then (1 : BitVec 32) else 0)))]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    underflow_prefix left right output frame entered enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have inputSame : ∀ reference ∈ [left, right], inputValue entered reference = inputValue memory reference := by
    intro reference member
    exact call.input_value_after_setup setup member
  have flagSame : (if (inputValue entered left).toNat < (inputValue entered right).toNat then (1 : BitVec 32) else 0) = (if (inputValue memory left).toNat < (inputValue memory right).toNat then (1 : BitVec 32) else 0) := by
    simp only [inputSame left (by simp), inputSame right (by simp)]
  rw [flagSame] at finished
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, leaveFrame frame after, ?_, ?_, ?_, ?_⟩
  · simpa only [decide_eq_true_eq] using
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
    have math := resultValue
    rw [inputSame left (by simp), inputSame right (by simp)] at math
    simpa only [inputValue, bytes] using math
  · exact (retained.access output old 32 1 true).trans resultWritable
  · intro id bound offset outside
    exact (retained.cells id bound offset).trans
      ((resultFootprint id (Nat.lt_of_lt_of_le bound fresh.1.next) offset outside).trans (before.cells id bound offset))

#print axioms underflow_prefix
#print axioms underflow_return
#print axioms underflow_contract_of_reporting
end UInt256Proof.Subtract.Safety
