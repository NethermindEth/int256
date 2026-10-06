import Extracted
import UInt256.Methods.Add.ScalarReportingResult
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import CIL.Safety.Certificate

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem scalar_entry_prefix (left right output : Reference) (frame : Frame) (memory : CIL.Safety.Memory)
  (call : CallingConditions Extracted.program memory [left, right] [output])
  (post : CIL.Safety.Memory → List Value → Prop)
  (continuation : ∃ fuel final values,
    run Extracted.program fuel Extracted.entryIndex 29 (binaryArguments left right output)
      frame [.scalar (.i32 0), .reference (.address output), .reference (.address right),
        .reference (.address left)] memory = .ok (final, values) ∧ post final values) :
  ∃ fuel final values,
    run Extracted.program fuel Extracted.entryIndex 0 (binaryArguments left right output)
      frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, binaryArguments, step, checkedValue, numericValue, formValue, fl, fr, fo,
            pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_entry_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : CIL.Safety.Memory) :
  run Extracted.program 2 Extracted.entryIndex (29 + 1) args frame [.scalar (.i32 flag)] memory =
    .ok (leaveFrame frame memory, []) := by
  simp only [Nat.reduceAdd]
  apply Eq.trans
  · apply run_next
    · simp only [cil_code]; rfl
    · simp only [cil_code]; rfl
    · simp [step, pureArity, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [run]
    simp [cil_code, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]



/-- Complete the public feature guard, certified dispatcher invocation and
  discarded scalar return, leaving only the public postcondition to discharge. -/
theorem scalar_entry_dispatch
    (child : ∀ memory left right output,
      CallingConditions Extracted.program memory [left, right] [output] →
      ∃ fuel final returned,
        InvocationCertificate Extracted.program Extracted.addScalarIndex
          (binaryArguments left right output ++ [.scalar (.i32 0)]) memory fuel final returned ∧
        ARMScalarReportingPost memory final returned left right output 0)
  (memory : Memory) (frame : Frame) (left right output : Reference)
  (call : CallingConditions Extracted.program memory [left, right] [output])
  (post : Memory → List Value → Prop)
  (continuation : ∀ childFuel final returned,
    InvocationCertificate Extracted.program Extracted.addScalarIndex
      ((binaryArguments left right output ++ [.scalar (.i32 0)])) memory childFuel final returned →
    ARMScalarPost memory final returned left right output →
    post (leaveFrame frame final) []) :
  ∃ fuel final returned,
    run Extracted.program fuel Extracted.entryIndex 0 (binaryArguments left right output)
      frame [] memory = .ok (final, returned) ∧ post final returned := by
  apply scalar_entry_prefix left right output frame memory call post
  obtain ⟨childFuel, final, returned, certified, result⟩ :=
    child memory left right output call
  obtain ⟨returnedFlag, shape⟩ := result.scalar
  subst returned
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by rfl
  have fetched : Extracted.entryBody.code[29]? = some (.call Extracted.addScalarIndex 4) := by rfl
  have stepped : step Extracted.entryBody (.call Extracted.addScalarIndex 4) 29
      (binaryArguments left right output) frame
      [.scalar (.i32 0), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (.call Extracted.addScalarIndex ((binaryArguments left right output ++ [.scalar (.i32 0)])) [] memory) := by
    simp [step, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨childFuel, certified.1⟩
    ⟨2, scalar_entry_return (binaryArguments left right output) returnedFlag frame final⟩
  exact ⟨fuel, leaveFrame frame final, [], executed,
    continuation childFuel final [.scalar (.i32 returnedFlag)] certified result.toARMScalarPost⟩

#print axioms scalar_entry_dispatch

#print axioms scalar_entry_prefix
#print axioms scalar_entry_return
end UInt256Proof.Add.Safety
