import UInt256.Methods.Shift.SafetySetup
import UInt256.Safety.OutputInitialization
import CIL.Safety.AccessBelow

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Separation is required only when the extracted body writes before reading
    its operand. Returning operators establish it from their private output. -/
def InitializationAllowed (input output : Reference) : Prop :=
  shiftCountEnd = shiftSnapshotPc ∨ input.allocation ≠ output.allocation

theorem shift_initialization (memory : Memory) (input output : Reference)
    (frame : Frame) (args : List Value) (inputs outputs : List Reference)
    (argument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions Extracted.program memory inputs outputs) (member : output ∈ outputs)
    (allowed : InitializationAllowed input output) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      CallingConditions Extracted.program after inputs outputs →
      (∀ offset, after.cells input.allocation offset = memory.cells input.allocation offset) →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = memory.cells id offset) →
      (∀ watermark, AccessBelow watermark memory after) →
      (∀ reference width alignment bytes, reference.allocation ≠ output.allocation →
        read memory reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      memory.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run Extracted.program fuel shiftIndex (shiftPc 27) args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run Extracted.program fuel shiftIndex shiftCountEnd args frame [] memory =
      .ok (final, returned) ∧ post final returned := by
  first
  | have same : shiftCountEnd = shiftPc 27 := by rfl
    rw [same]
    exact continuation memory call (fun _ => rfl) (fun _ _ _ => rfl)
      (fun watermark => (MemoryBelow.refl watermark memory).accessBelow) (fun _ _ _ _ _ loaded => loaded) (Nat.le_refl _)
  | apply output_initialization_prefix Extracted.program shiftIndex shiftCountEnd 2 shiftBody frame args
      memory inputs outputs output 0 call member (by rfl) argument
      (by
        intro i
        have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) post
    intro after written valid outside
    have different : input.allocation ≠ output.allocation := allowed.resolve_left (by decide)
    apply continuation after valid (fun offset => outside input.allocation offset (Or.inl different)) outside
      (fun watermark => write_preserves_access_below written watermark) ?_ (write_extends_allocations _ _ _ _ _ written).next
    intro reference width alignment bytes separate loaded
    exact write_preserves_disjoint_read written loaded (Or.inl separate)

#print axioms shift_initialization
end UInt256Proof.Shift.Safety
