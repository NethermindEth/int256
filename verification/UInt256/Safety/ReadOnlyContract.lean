import CIL.Safety.Certificate
import UInt256.Safety.Calling

namespace UInt256Model.Safety

open CIL.Safety

def readOnlyArguments (inputs : List Reference) : List Value :=
  inputs.map fun reference => .reference (.address reference)

/-- Initial-input result and preservation of every pre-existing caller cell,
    with finite checked execution and reference/lifetime invariants. -/
def ReadOnlyContract (operation : List (BitVec 256) → CIL.Value)
    (program : CIL.Program) (method : Nat) (arity : Nat) : Prop :=
  ∀ (memory : Memory) (inputs : List Reference), inputs.length = arity →
    CallingConditions program memory inputs [] →
    ∃ fuel final,
      InvocationCertificate program method (readOnlyArguments inputs) memory fuel final
        [.scalar (operation (inputs.map (inputValue memory)))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset,
        final.cells id offset = memory.cells id offset

theorem CallingConditions.readOnly_arguments_valid {program : CIL.Program}
    {memory : Memory} {inputs : List Reference}
    (call : CallingConditions program memory inputs []) :
    ValuesValid memory (readOnlyArguments inputs) := by
  intro value member
  change value ∈ inputs.map (fun reference => Value.reference (.address reference)) at member
  obtain ⟨reference, referenceMember, rfl⟩ := List.mem_map.mp member
  exact call.input_formed referenceMember

theorem CallingConditions.readOnly_setup_succeeds {program : CIL.Program}
    {memory : Memory} {inputs : List Reference} {body : CIL.Method}
    (call : CallingConditions program memory inputs [])
    (fits : FrameSetupFits body (readOnlyArguments inputs)) :
    ∃ frame entered, enterFrame body (readOnlyArguments inputs) memory = .ok (frame, entered) ∧
      LiveState program (readOnlyArguments inputs) frame [] entered :=
  enterFrame_live_succeeds _ _ _ _ call.1.1 call.readOnly_arguments_valid call.2 fits

#print axioms CallingConditions.readOnly_arguments_valid
#print axioms CallingConditions.readOnly_setup_succeeds

end UInt256Model.Safety
