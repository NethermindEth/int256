import UInt256.Safety.NumericStore
import UInt256.Methods.AddSubtract.VectorSetup
import UInt256.Safety.CallerSetup
import UInt256.Safety.OutputAccess
import CIL.Safety.AccessBelow

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Store a checked numeric value in an extracted private slot, retaining the
    current caller bytes and the access authority for all other locals. -/
theorem vector_local_store (boundary : Nat) (entered current : CIL.Safety.Memory)
    (inputs outputs : List Reference) (frame : Frame)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec)
    (specified : vectorSpecs[index]? = some spec)
    (value : CIL.Value) (number : Nat)
    (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 =
        .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions Extracted.program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step vectorBody (.setLocal index) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) :=
  checked_numeric_store Extracted.program vectorBody vectorSpecs boundary entered current
    inputs outputs frame currentCall enteredWF homes authority index spec specified value number fits

#print axioms vector_local_store

/-- Store a checked numeric value in an extracted private slot, retaining the
    initial caller snapshot and the access authority for all other locals. -/
theorem vector_private_store (original entered current : CIL.Safety.Memory)
    (inputs outputs : List Reference) (frame : Frame)
    (_call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec)
    (specified : vectorSpecs[index]? = some spec)
    (value : CIL.Value) (number : Nat)
    (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 =
        .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow original.nextIdentity original after ∧
      CallingConditions Extracted.program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step vectorBody (.setLocal index) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stepped⟩ :=
    vector_local_store original.nextIdentity entered current inputs outputs frame currentCall
      enteredWF homes authority index spec specified value number fits
  exact ⟨reference, after, slot, loaded, preserved.trans retained, afterCall, afterAuthority, written, stepped⟩

#print axioms vector_private_store
end UInt256Proof.AddSubtract.Safety
