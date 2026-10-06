import CIL.Safety.Execution

namespace CIL.Safety

/-- A word-valued conditional branch checks the scalar operand and preserves memory. -/
theorem step_word_nonzero (body : CIL.Method) (pc target : Nat) (args : List Value)
    (frame : Frame) (value : BitVec 64) (memory : Memory) :
    step body (.brnonzero target) pc args frame [.scalar (.i64 value)] memory =
      .ok (.next (if value = 0 then pc + 1 else target) [] frame memory) := by
  simp [step, pureArity, numericValue, scalars, CIL.step, CIL.truth, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

#print axioms step_word_nonzero
end CIL.Safety
