import CIL.Safety.Execution

namespace UInt256Proof.Safety

/-- Generates the interpreter's equation lemmas once so importers reuse them instead of regenerating
    tens of megabytes each; macros naming `CIL.step.eq_def` cannot generate it themselves. -/
theorem interpreter_equations_available : True := by
  have := @CIL.step.eq_def
  have := @CIL.Safety.step.eq_1
  have := @CIL.Safety.instruction.eq_1
  have := @CIL.Safety.pureArity.eq_1
  have := @CIL.Safety.memoryInstruction.eq_1
  have := @CIL.Safety.staticInstruction.eq_1
  have := @CIL.Safety.scalars.eq_1
  have := @CIL.binary.eq_1
  have := @CIL.unary.eq_1
  trivial

end UInt256Proof.Safety
