import Extracted
import UInt256.Safety.PrivateWordSteps
import UInt256.Safety.Contract
import UInt256.Arithmetic.Carry
import CIL.Safety.WordFrameSetup
import CIL.Safety.Certificate

namespace UInt256Proof.Add.FixtureStraightLine
open CIL.Safety UInt256Model.Safety

def specs : List (Option (BitVec 64)) := List.replicate 17 (some 0)

theorem frame_setup (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame Extracted.method0 (binaryArguments left right output) memory = .ok (frame, entered) ∧
      LiveState Extracted.program (binaryArguments left right output) frame [] entered ∧
      WritableHomes entered memory.nextIdentity (wordKinds specs) frame.locals ∧ entered.WellFormed := by
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds (body := Extracted.method0)
    (by simp [cil_code, Extracted.method0, FrameSetupFits, InitializersFit, InitializerFits,
      AggregateArgumentsFit, ParameterArgumentsFit])
  obtain ⟨frame', entered', setup', homes, _, wf⟩ := word_frame_setup Extracted.method0 specs
    (by rfl) (by rfl) (by rfl) (by rfl) memory (binaryArguments left right output) call.1.1
  rw [setup] at setup'
  cases setup'
  exact ⟨frame, entered, setup, live, writable_of_word_homes homes (by simp [specs]), wf⟩

theorem body_run (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame Extracted.method0 (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WritableHomes entered memory.nextIdentity (wordKinds specs) frame.locals)
    (enteredWF : entered.WellFormed) :
    ∃ fuel result returned,
      run Extracted.program fuel 0 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧
      OutputResult memory result output (inputValue memory left + inputValue memory right) returned := by
  have found : Extracted.program[0]? = some Extracted.method0 := by rfl
  have state := PrivateWords.initial call setup
  let post := fun result returned =>
    OutputResult memory result output (inputValue memory left + inputValue memory right) returned
  iterate 101 private_word_step
  have owned := fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  apply state.finish_words call homes owned found (position := 2) rfl (by rfl) rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue, ← UInt256Proof.sumWords_sum]
  generalize inputLimb memory left = a
  generalize inputLimb memory right = b
  simp only [← UInt256Proof.carry_zero]
  have hc1 := UInt256Proof.carry_bound (a 0) (b 0) 0#64 (by decide)
  have hc2 := UInt256Proof.carry_bound (a 1) (b 1) _ hc1
  rw [UInt256Proof.carry_flags_or (a 1) (b 1) _ hc1, UInt256Proof.carry_flags_or (a 2) (b 2) _ hc2]
  rfl

theorem correctness : WrappingBinaryContract (· + ·) Extracted.program 0 := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live, homes, wf⟩ := frame_setup memory left right output call
  obtain ⟨fuel, final, returned, finished, result⟩ := body_run memory entered left right output frame call setup homes wf
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain rfl := result.returns
  exact ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ (by rfl) checked setup live finished,
    result.value, result.writable, result.footprint⟩

#print axioms correctness
end UInt256Proof.Add.FixtureStraightLine
