import UInt256.Methods.Bitwise.NotVectorSafety
import UInt256.Safety.CallerSetup
import UInt256.Safety.InitializedOutput

namespace UInt256Proof.Bitwise.NotSafety
open CIL.Safety UInt256Model.Safety


theorem vector_initialized : InitializedUnaryContract (fun input => ~~~input) Extracted.program vectorIndex := by
  intro memory input output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have kinds : vectorBody.localKinds = [] := by rfl
  have values : vectorBody.locals = [] := by rfl
  have arguments : vectorBody.aggregateArgs = [] := by rfl
  have setup : enterFrame vectorBody (unaryArguments input output) memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, values, arguments, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have checked : (unaryArguments input output).mapM (checkedValue memory) =
      .ok (unaryArguments input output) := by
    have fl := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [unaryArguments, checkedValue, formValue, fl, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨final, finished, retained, outside, readback⟩ := vector_run memory input output frame call
  simp only [leaveFrame, frame, List.foldl_nil] at finished
  refine ⟨8, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    readback, ?_, ?_⟩
  · exact retained.1.2.2 (wordView output) (by simp)
  · intro id _ offset beyond
    exact outside id offset beyond

#print axioms vector_initialized
end UInt256Proof.Bitwise.NotSafety
