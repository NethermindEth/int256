import UInt256.Methods.Subtract.ScalarFinish
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Complete checked invocation of the large-right scalar branch, including
    initial-input arithmetic, the exact borrow and caller storage preservation. -/
theorem scalar_general_checked (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (large : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ ScalarResult memory final values left right output := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    scalar_frame_setup memory (binaryArguments left right output) call.1.1
  obtain ⟨fuel, final, values, finished, satisfied⟩ := scalar_general_borrows memory entered left right output
    frame call setup homes large (fun final values => ScalarResult memory final values left right output)
    (fun borrowHome results current state =>
      scalar_finish memory entered current frame left right output borrowHome results call setup state)
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  exact ⟨fuel, final, values,
    by simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished,
    satisfied⟩

#print axioms scalar_general_checked
end UInt256Proof.Subtract.Safety
