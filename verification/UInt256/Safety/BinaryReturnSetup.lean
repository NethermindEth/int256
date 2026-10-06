import UInt256.Safety.ReadOnlyForwarder
import UInt256.Safety.ConstructorSetup
import CIL.Safety.NumericHomes

namespace UInt256Model.Safety
open CIL.Safety UInt256Model.Safety

def binaryResultSpecs : List NumericLocalSpec := [⟨.vector256, .v256 0, 0, by rfl⟩]

theorem binary_return_setup (program : CIL.Program) (body : CIL.Method)
    (kinds : body.localKinds = numericKinds binaryResultSpecs)
    (values : body.locals = numericInitializers binaryResultSpecs)
    (arguments : body.aggregateArgs = []) (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ frame entered temporary,
      enterFrame body (readOnlyArguments [left, right]) memory = .ok (frame, entered) ∧
      frame.locals = [.bytes .vector256 temporary] ∧
      memory.nextIdentity ≤ temporary.allocation ∧
      CallingConditions program entered [left, right] [temporary] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity binaryResultSpecs call.1.1
  cases homes with
  | cons temporary spec fresh loaded writable tail =>
    cases tail
    let frame : Frame := ⟨memory.nextIdentity, [.bytes .vector256 temporary], owned, []⟩
    have setup : enterFrame body (readOnlyArguments [left, right]) memory = .ok (frame, entered) := by
      simp [enterFrame, kinds, values, arguments, made, makeArgumentHomes, frame,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    have enteredCall := (call.after_frame_setup setup).with_writable_output writable
    exact ⟨frame, entered, temporary, setup, rfl, fresh, enteredCall,
      enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms binary_return_setup
end UInt256Model.Safety
