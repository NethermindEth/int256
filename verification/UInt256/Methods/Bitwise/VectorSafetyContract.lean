import UInt256.Methods.Bitwise.VectorSafety
import UInt256.Safety.CallerSetup
import UInt256.Safety.InitializedOutput

namespace UInt256Proof.Bitwise.Safety
open CIL.Safety UInt256Model.Safety


theorem vector_initialized : InitializedBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation) Extracted.program vectorIndex := by
  intro memory left right output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have kinds : vectorBody.localKinds = [] := by rfl
  have values : vectorBody.locals = [] := by rfl
  have arguments : vectorBody.aggregateArgs = [] := by rfl
  have setup : enterFrame vectorBody (binaryArguments left right output) memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, values, arguments, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨final, finished, retained, outside, readback⟩ := vector_run memory left right output frame call
  simp only [leaveFrame, frame, List.foldl_nil] at finished
  refine ⟨11, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    readback, ?_, ?_⟩
  · exact retained.1.2.2 (wordView output) (by simp)
  · intro id _ offset beyond
    exact outside id offset beyond

theorem vector_checked : WrappingBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation)
    Extracted.program vectorIndex := vector_initialized.to_wrapping

#print axioms vector_initialized
#print axioms vector_checked
end UInt256Proof.Bitwise.Safety
