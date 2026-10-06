import Extracted
import CIL.Safety.NumericHomes
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def portableIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.vector (.extractMSB64 256)) _ => true | _ => false

def portableBody : CIL.Method := Extracted.program[portableIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def portableSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, by rfl⟩, ⟨.word32, .i32 0, 0, by rfl⟩,
   ⟨.word32, .i32 0, 0, by rfl⟩]

/-- Prepare the three extracted local homes with distinct identities, without
replacing caller inputs by disjoint synthetic values. -/
theorem portable_setup (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ frame entered,
      enterFrame portableBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity portableSpecs frame.locals ∧
      CallingConditions Extracted.program entered [left, right] [] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity portableSpecs call.1.1
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have kinds : portableBody.localKinds = numericKinds portableSpecs := by rfl
  have values : portableBody.locals = numericInitializers portableSpecs := by rfl
  have aggregates : portableBody.aggregateArgs = [] := by rfl
  have setup : enterFrame portableBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) := by
    simp [enterFrame, kinds, values, aggregates, made, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨frame, entered, setup, homes, call.after_frame_setup setup,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms portable_setup
end UInt256Proof.Compare.Safety
