import CIL.Safety.RelocationAddress
import CIL.Safety.Execution

namespace CIL.Safety

/- These are placement-independence theorems for the actual checked interpreter.
References keep allocation identity and offset; a moving runtime must update their
physical representations accordingly. Neither GC implementation correctness nor
availability of physical space for future allocations is proved here. -/

theorem relocation_preserves_step (m : PlacedMemory) (after : Placement)
    (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) :
    step body op pc args frame stack (relocate m after).memory =
      step body op pc args frame stack m.memory := rfl

theorem relocation_preserves_execution (m : PlacedMemory) (after : Placement)
    (program : CIL.Program) (fuel method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) :
    run program fuel method pc args frame stack (relocate m after).memory =
      run program fuel method pc args frame stack m.memory := rfl

theorem relocation_preserves_invocation (m : PlacedMemory) (after : Placement)
    (program : CIL.Program) (fuel method : Nat) (args : List Value) :
    invoke program fuel method args (relocate m after).memory =
      invoke program fuel method args m.memory := rfl

#print axioms relocation_preserves_step
#print axioms relocation_preserves_execution
#print axioms relocation_preserves_invocation
end CIL.Safety
