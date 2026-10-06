import Extracted
import CIL.Safety.NumericHomes

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety

def vector128Index : Nat := Extracted.program.findIdx fun body =>
  (body.code.any fun op => match op with | .memory .load128 => true | _ => false) &&
  body.code.any fun op => match op with
    | .intrinsic (.vector (.add64 128)) _ | .intrinsic (.vector (.sub64 128)) _ => true
    | _ => false

def vector128Body : CIL.Method := Extracted.program[vector128Index]?.getD
  { code := [], locals := [], returnsValue := false }

def vector128Specs : List NumericLocalSpec := numericSpecs vector128Body

theorem vector128_local_metadata :
    vector128Body.localKinds = .reference :: vector128Specs.map NumericLocalSpec.kind ∧
    vector128Body.locals = .nullRef :: vector128Specs.map NumericLocalSpec.value := by
  constructor <;> rfl

/-- The extracted reference root remains distinct from initialized numeric homes.
    All homes are fresh; setup leaves the caller's bytes unchanged. -/
theorem vector128_frame_setup (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered slots,
      enterFrame vector128Body args memory = .ok (frame, entered) ∧
      frame.locals = .root (some .null) :: slots ∧
      NumericHomes entered memory.nextIdentity vector128Specs slots ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity vector128Specs wf
  simp only [numericKinds, numericInitializers] at made
  let frame : Frame := ⟨memory.nextIdentity, .root (some .null) :: slots, owned, []⟩
  have arguments : vector128Body.aggregateArgs = [] := by rfl
  have setup : enterFrame vector128Body args memory = .ok (frame, entered) := by
    simp only [enterFrame, vector128_local_metadata.1, vector128_local_metadata.2,
      makeLocals, makeLocal, made, arguments, makeArgumentHomes,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.nil_append, List.append_nil]
    rfl
  exact ⟨frame, entered, slots, setup, rfl, homes,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup,
    enterFrame_preserves_wellFormed _ _ _ _ _ wf setup⟩

#print axioms vector128_local_metadata
#print axioms vector128_frame_setup
end UInt256Proof.AddSubtract.Safety
