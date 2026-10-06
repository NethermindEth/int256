import Extracted
import UInt256.Safety.ReadOnlyForwarder
import UInt256.Safety.ConstructorSetup
import CIL.Safety.NumericHomes

namespace UInt256Proof.Bitwise.NotSafety
open CIL.Safety UInt256Model.Safety

def resultSpecs : List NumericLocalSpec := [⟨.vector256, .v256 0, 0, by rfl⟩]

theorem return_setup (memory : Memory) (input : Reference)
    (call : CallingConditions Extracted.program memory [input] []) :
    ∃ frame entered temporary,
      enterFrame Extracted.entryBody (readOnlyArguments [input]) memory = .ok (frame, entered) ∧
      frame.locals = [.bytes .vector256 temporary] ∧
      memory.nextIdentity ≤ temporary.allocation ∧
      CallingConditions Extracted.program entered [input] [temporary] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity resultSpecs call.1.1
  cases homes with
  | cons temporary spec fresh loaded writable tail =>
    cases tail
    let frame : Frame := ⟨memory.nextIdentity, [.bytes .vector256 temporary], owned, []⟩
    have kinds : Extracted.entryBody.localKinds = numericKinds resultSpecs := by rfl
    have values : Extracted.entryBody.locals = numericInitializers resultSpecs := by rfl
    have arguments : Extracted.entryBody.aggregateArgs = [] := by rfl
    have setup : enterFrame Extracted.entryBody (readOnlyArguments [input]) memory = .ok (frame, entered) := by
      simp [enterFrame, kinds, values, arguments, made, makeArgumentHomes, frame,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    have enteredCall := (call.after_frame_setup setup).with_writable_output writable
    exact ⟨frame, entered, temporary, setup, rfl, fresh, enteredCall,
      enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms return_setup
end UInt256Proof.Bitwise.NotSafety
