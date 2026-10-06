import CIL.Safety.Frames
import CIL.Safety.WriteEffects

namespace CIL.Safety

/-- Storing a supported numeric value initializes its entire typed local home. -/
theorem store_numeric_local {memory : Memory} {reference : Reference}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (ready : access memory reference (localWidth kind) 1 true = .ok ()) :
    ∃ result,
      write memory reference (numberBytes number (localWidth kind)) 1 = .ok result ∧
      storeLocal memory (.bytes kind reference) (.scalar value) =
        .ok (.bytes kind reference, result) ∧
      read result reference (localWidth kind) 1 = .ok (numberBytes number (localWidth kind)) := by
  have length : (numberBytes number (localWidth kind)).length = localWidth kind := by simp [numberBytes]
  obtain ⟨result, written⟩ := write_succeeds (bytes := numberBytes number (localWidth kind))
    (by simpa only [length] using ready)
  have loaded := write_readback _ _ _ _ _ written
  rw [length] at loaded
  refine ⟨result, written, ?_, loaded⟩
  simp [storeLocal, fits, written, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms store_numeric_local

end CIL.Safety
