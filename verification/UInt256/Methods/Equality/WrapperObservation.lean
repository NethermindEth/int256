import UInt256.Methods.Equality.PrimitiveOperator
import CIL.Safety.CallComposition

/-!
Transport a checked Boolean observation through an equality wrapper. Counterexamples
can execute the child once and compose argument reversal and polarity without unfolding it again.
-/

namespace UInt256Proof.Equality.WrapperObservation
open CIL.Safety

/-- A forwarding wrapper preserves a child's Boolean observation, with its declared polarity. -/
theorem forward (profile : CIL.FeatureProfile) (reversed negate flag : Bool)
    (program : CIL.Program) (entry callee childFuel : Nat)
    (found : program[entry]? = some (PrimitiveOperator.body profile reversed negate callee))
    (memory : Memory) (left right : Value)
    (leftChecked : checkedValue memory left = .ok left)
    (rightChecked : checkedValue memory right = .ok right)
    (leftKnown : left.hasUnspecified = false) (rightKnown : right.hasUnspecified = false)
    (child : ∃ final, invoke program childFuel callee
      (if reversed then [right, left] else [left, right]) memory =
        .ok (final, [.scalar (.i32 (if flag then 1 else 0))])) :
    ∃ fuel final, invoke program fuel entry [left, right] memory =
      .ok (final, [.scalar (.i32 (if flag != negate then 1 else 0))]) := by
  let frame : Frame := {
    activation := memory.nextIdentity
    locals := []
    owned := []
    arguments := []
    stackBytes := 0 }
  have setup : enterFrame (PrimitiveOperator.body profile reversed negate callee)
      [left, right] memory = .ok (frame, memory) := by
    simp [enterFrame, PrimitiveOperator.body, makeSelectedLocals, makeLocals,
      makeArgumentHomes, makeParameterHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have checked : [left, right].mapM (checkedValue memory) = .ok [left, right] := by
    simp [leftChecked, rightChecked, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨final, observed⟩ := child
  have stepped : step (PrimitiveOperator.body profile reversed negate callee) (.call callee 2)
      2 [left, right] frame (if reversed then [left, right] else [right, left]) memory =
      .ok (.call callee (if reversed then [right, left] else [left, right]) [] memory) := by
    cases reversed <;>
      simp [step, cil_guard, observerCount, leftChecked, rightChecked, leftKnown, rightKnown,
        unspecifiedOperands, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found (by cases reversed <;> rfl) stepped
    ⟨childFuel, observed⟩
    ⟨3, PrimitiveOperator.returned profile reversed negate program entry callee found
      [left, right] flag frame final⟩
  have firstStep : step (PrimitiveOperator.body profile reversed negate callee)
      (.arg (if reversed then 1 else 0)) 0 [left, right] frame [] memory =
      .ok (.next 1 [if reversed then right else left] frame memory) := by
    cases reversed <;> simp [step_argument_eq, leftChecked, rightChecked,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have secondStep : step (PrimitiveOperator.body profile reversed negate callee)
      (.arg (if reversed then 0 else 1)) 1 [left, right] frame
      [if reversed then right else left] memory =
      .ok (.next 2 (if reversed then [left, right] else [right, left]) frame memory) := by
    cases reversed <;> simp [step_argument_eq, leftChecked, rightChecked,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨tailFuel + 2, leaveFrame frame final, invoke_of_run found checked setup
    ((run_next found (by rfl) firstStep).trans
      ((run_next found (by rfl) secondStep).trans tail))⟩
#print axioms forward
end UInt256Proof.Equality.WrapperObservation
