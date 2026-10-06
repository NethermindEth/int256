import Extracted
import UInt256.Safety.ConstructorSetup
import CIL.Safety.NumericHomes

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def primitiveSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, by rfl⟩, ⟨.vector256, .v256 0, 0, by rfl⟩]

theorem primitive_frame_setup (memory : Memory) (input : Reference) (args : List Value)
    (call : CallingConditions Extracted.program memory [input] []) :
    ∃ frame entered operand output,
      enterFrame Extracted.entryBody args memory = .ok (frame, entered) ∧
      frame.locals = [.bytes .vector256 operand, .bytes .vector256 output] ∧
      memory.nextIdentity ≤ operand.allocation ∧ operand.allocation < output.allocation ∧
      access entered operand 32 1 true = .ok () ∧
      CallingConditions Extracted.program entered [input] [output] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity primitiveSpecs call.1.1
  cases homes with
  | cons operand spec fresh loaded writable tail =>
    cases tail with
    | cons output spec2 later loaded2 writable2 tail2 =>
      cases tail2
      let frame : Frame := ⟨memory.nextIdentity,
        [.bytes .vector256 operand, .bytes .vector256 output], owned, []⟩
      have kinds : Extracted.entryBody.localKinds = numericKinds primitiveSpecs := by rfl
      have values : Extracted.entryBody.locals = numericInitializers primitiveSpecs := by rfl
      have arguments : Extracted.entryBody.aggregateArgs = [] := by rfl
      have setup : enterFrame Extracted.entryBody args memory = .ok (frame, entered) := by
        simp [enterFrame, kinds, values, arguments, made, makeArgumentHomes, frame,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨frame, entered, operand, output, setup, rfl, fresh, later, writable,
        (call.after_frame_setup setup).with_writable_output writable2,
        enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms primitive_frame_setup
end UInt256Proof.Multiply.Safety
