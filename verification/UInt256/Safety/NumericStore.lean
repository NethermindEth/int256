import UInt256.Safety.CallerSetup
import UInt256.Safety.OutputAccess
import CIL.Safety.NumericHomes
import CIL.Safety.AccessBelow

namespace UInt256Model.Safety
open CIL.Safety

/-- Store a checked numeric value in an extracted private slot, retaining the
    current caller bytes and the access authority for all other locals. -/
theorem checked_numeric_home_store (program : CIL.Program) (body : CIL.Method)
    (boundary : Nat) (entered current : CIL.Safety.Memory)
    (inputs outputs : List Reference) (frame : Frame)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec)
    (reference : Reference)
    (slot : frame.locals[index]? = some (.bytes spec.kind reference))
    (bound : boundary ≤ reference.allocation)
    (writable : access entered reference (localWidth spec.kind) 1 true = .ok ())
    (value : CIL.Value) (number : Nat)
    (fits : localNumber spec.kind value = .ok number) :
    ∃ after,
      read after reference (localWidth spec.kind) 1 =
        .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step body (.setLocal index) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have old := (enteredWF.1 reference.allocation allocation ready.present).1
  have permitted := authority.access writable old
  obtain ⟨after, stepped, written, loaded⟩ := step_store_numeric_local
    (body := body) (pc := 0) (args := []) (rest := [])
    spec.kind value number fits slot permitted
  have caller := write_preserves_memory_below _ _ _ _ _ _ bound written
  refine ⟨after, loaded, caller,
    currentCall.after_write written,
    authority.trans (write_preserves_access_below written _), written, ?_⟩
  intro pc args rest
  obtain ⟨result, stepResult, sameWrite, _⟩ := step_store_numeric_local
    (body := body) (pc := pc) (args := args) (rest := rest)
    spec.kind value number fits slot permitted
  rw [written] at sameWrite
  cases sameWrite
  exact stepResult

/-- Numeric-only frames obtain the checked home from their initialization recipe. -/
theorem checked_numeric_store (program : CIL.Program) (body : CIL.Method)
    (specs : List NumericLocalSpec) (boundary : Nat) (entered current : CIL.Safety.Memory)
    (inputs outputs : List Reference) (frame : Frame)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec)
    (specified : specs[index]? = some spec)
    (value : CIL.Value) (number : Nat)
    (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 =
        .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step body (.setLocal index) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.home_at index spec specified
  obtain ⟨after, result⟩ := checked_numeric_home_store program body boundary entered current
    inputs outputs frame currentCall enteredWF authority index spec reference slot bound writable value number fits
  exact ⟨reference, after, slot, result⟩

#print axioms checked_numeric_home_store
#print axioms checked_numeric_store
end UInt256Model.Safety
