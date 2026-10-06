import CIL.Safety.NumericLocalStore
import UInt256.Safety.ArgumentValues
import UInt256.Safety.OutputAccess
import CIL.Safety.MemoryBelow

namespace UInt256Model.Safety

open CIL.Safety

/-- A private aggregate local receives a fully initialized value without changing
    any older input. Separation is proved from allocation identities by callers. -/
theorem CallingConditions.store_private_aggregate {program : CIL.Program}
    {memory : Memory} {inputs outputs : List Reference} (home : Reference) (bits : BitVec 256)
    (call : CallingConditions program memory inputs outputs)
    (writable : access memory home 32 1 true = .ok ())
    (older : ∀ reference ∈ inputs, reference.allocation < home.allocation) :
    ∃ result,
      storeLocal memory (.bytes .vector256 home) (.scalar (.v256 bits)) =
        .ok (.bytes .vector256 home, result) ∧
      CallingConditions program result (inputs ++ [home]) outputs ∧
      inputValue result home = bits ∧
      (∀ reference ∈ inputs, inputValue result reference = inputValue memory reference) ∧
      MemoryBelow home.allocation memory result := by
  obtain ⟨result, written, stored, loaded⟩ :=
    store_numeric_local .vector256 (.v256 bits) bits.toNat rfl writable
  have preserved := write_preserves_memory_below _ _ _ _ _ home.allocation (Nat.le_refl _) written
  refine ⟨result, stored, (call.after_write written).with_readable_input loaded,
    inputValue_of_encoded_read loaded, ?_, preserved⟩
  intro reference member
  have same : (fun offset => (result.cells reference.allocation offset).bits) =
      (fun offset => (memory.cells reference.allocation offset).bits) := by
    funext offset
    rw [preserved.cells reference.allocation (older reference member) offset]
  simp only [inputValue, same]

#print axioms CallingConditions.store_private_aggregate

end UInt256Model.Safety
