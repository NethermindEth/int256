import CIL.Safety.Execution

namespace UInt256Proof.Safety

/-- Generates the per-opcode equations of `CIL.step` (about 20 MB) once, apart from the smaller
    interpreter equations, so only modules that unfold the dispatcher wait on it. -/
theorem dispatch_equations_available : True := by
  have := @CIL.step.eq_1
  trivial

end UInt256Proof.Safety
