import Extracted
import CIL.Safety.NumericHomes
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def nativeIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.avx512 _) _ => true | _ => false

def nativeBody : CIL.Method := Extracted.program[nativeIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def nativeUsesLess : Bool := nativeBody.code.any fun op =>
  match op with | .intrinsic (.avx512 .ltu64) _ => true | _ => false

def nativeInclusive : Bool := nativeBody.code.any fun op =>
  match op with | .const32 value => value == BitVec.ofNat 32 86 | _ => false

def nativeReturn : Nat := nativeBody.code.findIdx fun op =>
  match op with | .ret => true | _ => false

def nativeSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, by rfl⟩, ⟨.vector256, .v256 0, 0, by rfl⟩,
   ⟨.vector256, .v256 0, 0, by rfl⟩]

/-- Prepare the three extracted local homes with distinct identities, without
replacing caller inputs by disjoint synthetic values. -/
theorem native_setup (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ frame entered,
      enterFrame nativeBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity nativeSpecs frame.locals ∧
      CallingConditions Extracted.program entered [left, right] [] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity nativeSpecs call.1.1
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have kinds : nativeBody.localKinds = numericKinds nativeSpecs := by rfl
  have values : nativeBody.locals = numericInitializers nativeSpecs := by rfl
  have aggregates : nativeBody.aggregateArgs = [] := by rfl
  have setup : enterFrame nativeBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) := by
    simp [enterFrame, kinds, values, aggregates, made, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨frame, entered, setup, homes, call.after_frame_setup setup,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms native_setup
end UInt256Proof.Compare.Safety
