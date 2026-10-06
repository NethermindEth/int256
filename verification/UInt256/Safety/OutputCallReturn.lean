import UInt256.Safety.PrivateOutputReturn
import CIL.Safety.CallComposition

namespace UInt256Model.Safety
open CIL.Safety

/-- Compose an actual checked void call with the fetched caller return. The
    helper's result is transported across the caller's private-frame retirement. -/
theorem run_output_call {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack callArgs : List Value} {frame : Frame} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs [output] frame known)
    (originalCall : CallingConditions program original inputs [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (expected : BitVec 256)
    (found : program[method]? = some body)
    (fetched : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack current = .ok (.call callee callArgs [] current))
    (returnCode : body.code[pc + 1]? = some .ret)
    (void : body.returnsValue = false)
    (effect : ∃ fuel final,
      invoke program fuel callee callArgs current = .ok (final, []) ∧
      OutputResult current final output expected []) :
    ∃ fuel final returned,
      run program fuel method pc args frame stack current = .ok (final, returned) ∧
      OutputResult original final output expected returned := by
  obtain ⟨childFuel, final, invoked, result⟩ := effect
  have finished : run program 1 method (pc + 1) args frame [] final =
      .ok (leaveFrame frame final, []) := by
    rw [run]
    simp only [found, returnCode, step, void]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found fetched stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  exact ⟨fuel, leaveFrame frame final, [], ran, state.finish_output originalCall owned expected result⟩

#print axioms run_output_call
end UInt256Model.Safety
