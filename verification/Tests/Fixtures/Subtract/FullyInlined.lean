import Extracted
import UInt256.Safety.PrivateWordSteps
import UInt256.Arithmetic.Borrow

namespace UInt256Proof.Subtract.FixtureFullyInlined
open CIL.Safety UInt256Model.Safety

def specs : List (Option (BitVec 64)) := List.replicate 13 (some 0)

theorem body_run (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame Extracted.method0 (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WritableHomes entered memory.nextIdentity (wordKinds specs) frame.locals)
    (enteredWF : entered.WellFormed) :
    ∃ fuel result returned,
      run Extracted.program fuel 0 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧
      OutputResult memory result output (inputValue memory left - inputValue memory right) returned := by
  have found : Extracted.program[0]? = some Extracted.method0 := by rfl
  have state := PrivateWords.initial call setup
  let post := fun result returned =>
    OutputResult memory result output (inputValue memory left - inputValue memory right) returned
  have owned := fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  repeat' first
    | (apply run_if <;> intro branch)
    | private_word_finish
    | private_word_step
  all_goals rw [← leftValue, ← rightValue]
  · generalize inputLimb memory left = a
    generalize inputLimb memory right = b
    rw [← UInt256Proof.four_limb_difference]
    have hc1 : (if a 0 < b 0 then 1#64 else 0#64).toNat ≤ 1 := by split <;> decide
    rw [UInt256Proof.borrow_expression (a 1) (b 1) _ hc1,
      UInt256Proof.borrow_expression (a 2) (b 2) _ (UInt256Proof.borrow_bound _ _ _),
      ← UInt256Proof.borrow_initial_flag]
    rfl
  all_goals
    simp only [UInt256Model.value]
    bv_omega

theorem correctness : WrappingBinaryContract (· - ·) Extracted.program 0 :=
  word_locals_binary_contract _ _ 0 Extracted.method0 specs rfl rfl rfl rfl rfl (by simp [specs])
    (fun _ _ _ => by simp [Extracted.method0, FrameSetupFits, InitializersFit, InitializerFits,
      AggregateArgumentsFit, ParameterArgumentsFit]) body_run

#print axioms correctness
end UInt256Proof.Subtract.FixtureFullyInlined
