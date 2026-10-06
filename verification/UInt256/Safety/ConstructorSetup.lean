import CIL.Safety.ConstructSetup
import UInt256.Safety.CallerSetup

namespace UInt256Model.Safety

open CIL.Safety

theorem CallingConditions.with_writable_output {program : CIL.Program}
    {memory : Memory} {inputs outputs : List Reference} {reference : Reference}
    (call : CallingConditions program memory inputs outputs)
    (writable : access memory reference 32 1 true = .ok ()) :
    CallingConditions program memory inputs (outputs ++ [reference]) := by
  refine ⟨⟨call.1.1, call.1.2.1, ?_⟩, call.2⟩
  intro view member
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_singleton] at member
  rcases member with member | rfl
  · exact call.1.2.2 view member
  · exact writable

/-- Transfer ordinary call permissions through the actual constructor-allocation
    step; the new private home becomes the constructor's writable output. -/
theorem CallingConditions.new_value {program : CIL.Program} {body : CIL.Method}
    {method pc callee : Nat} {inputs : List Reference}
    (args arguments rest : List Value) (frame : Frame) (memory : Memory)
    (found : program[method]? = some body)
    (call : CallingConditions program memory inputs [])
    (checked : arguments.mapM (checkedValue memory) = .ok arguments) :
    ∃ temporary updated,
      step body (.newValue callee arguments.length) pc args frame (arguments.reverse ++ rest) memory =
        .ok (.construct callee (.reference (.address temporary) :: arguments) rest
          { frame with owned := temporary.allocation :: frame.owned } temporary updated) ∧
      CallingConditions program updated inputs [temporary] ∧
      read updated temporary 32 1 = .ok (numberBytes 0 32) ∧
      MemoryBelow memory.nextIdentity memory updated ∧
      temporary.allocation = memory.nextIdentity := by
  obtain ⟨temporary, updated, stepped, loaded, writable, preserved, fresh⟩ :=
    step_newValue args arguments rest frame memory call.1.1 checked
  have wf := step_preserves_wellFormed _ _ _ _ _ _ _ _ call.1.1 stepped
  have world := step_preserves_static_world _ _ _ _ _ _ _ _ _ call.1.1
    (program_static_sites_valid _ _ _ found) call.2 stepped
  exact ⟨temporary, updated, stepped,
    (call.after_memory_below preserved wf world).with_writable_output writable,
    loaded, preserved, fresh⟩

#print axioms CallingConditions.with_writable_output
#print axioms CallingConditions.new_value

end UInt256Model.Safety
