import CIL.Safety.ArgumentHomeValues
import CIL.Safety.Execution

namespace CIL.Safety

/-- The actual new-value step allocates initialized caller-owned storage and
    passes its checked address to the constructor. -/
theorem step_newValue {body : CIL.Method} {pc callee : Nat}
    (args arguments rest : List Value) (frame : Frame) (memory : Memory)
    (wellFormed : memory.WellFormed)
    (checked : arguments.mapM (checkedValue memory) = .ok arguments) :
    ∃ temporary updated,
      step body (.newValue callee arguments.length) pc args frame (arguments.reverse ++ rest) memory =
        .ok (.construct callee (.reference (.address temporary) :: arguments) rest
          { frame with owned := temporary.allocation :: frame.owned } temporary updated) ∧
      read updated temporary 32 1 = .ok (numberBytes 0 32) ∧
      access updated temporary 32 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory updated ∧
      temporary.allocation = memory.nextIdentity := by
  obtain ⟨temporary, allocated, updated, home, stored, _, loaded, writable, preserved⟩ :=
    allocate_initialized256 memory frame.activation (BitVec.ofNat 256 0) wellFormed
  refine ⟨temporary, updated, ?_, loaded, writable, preserved,
    (allocateHome_fresh _ _ _ _ _ home).2.1⟩
  simp [step, checked, localWidth, home, stored,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_newValue

end CIL.Safety
