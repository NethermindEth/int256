import UInt256.Methods.Shift.ScalarContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

def wrapperBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [],
    code := [.arg 0, .arg 1, .arg 2, .call callee 3, .ret] }

/-- The instance methods forward exactly the checked input, count and output. -/
theorem wrapper_correctness (profile : CIL.FeatureProfile) (direction : Direction)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (wrapperBody profile callee))
    (child : ShiftContract direction program callee) : ShiftContract direction program index := by
  intro memory input count output call
  obtain ⟨childFuel, final, certificate, value, writable, readable, outside⟩ :=
    child memory input count output call
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  let args := shiftArguments input count output
  have fi := call.input_formed (by simp : input ∈ [input])
  have fo := call.output_formed (by simp : output ∈ [output])
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, shiftArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (wrapperBody profile callee) args memory = .ok (frame, memory) := rfl
  have stepped : step (wrapperBody profile callee) (.call callee 3) 3 args frame args.reverse memory =
      .ok (.call callee args [] memory) := by
    simp [args, shiftArguments, step, cil_guard, observerCount, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run program 1 index 4 args frame [] final = .ok (final, []) :=
    run_return found (by rfl) (by rfl) (by rfl)
  obtain ⟨fuel, finished⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, certificate.1⟩ ⟨1, tail⟩
  have leading : run program (fuel + 3) index 0 args frame [] memory =
      run program fuel index 3 args frame args.reverse memory := by
    cil_checked_steps 3 [args, shiftArguments, fi, fo]
    rfl
  exact ⟨fuel + 3, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup) (leading.trans finished),
    value, writable, readable, outside⟩

#print axioms wrapper_correctness
end UInt256Proof.Shift.Safety
