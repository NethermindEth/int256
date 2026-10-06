import CIL.Safety.MemoryLemmas

namespace CIL.Safety

structure ArgumentView where
  reference : Reference
  width : Nat
  deriving DecidableEq, Repr

/-- Ordinary entry requirements, independent of the method body or its future
    execution. Output initialization is deliberately not required. -/
def ValidCall (m : Memory) (inputs outputs : List ArgumentView) : Prop :=
  m.WellFormed ∧
    (∀ input ∈ inputs, ∃ bytes, read m input.reference input.width 1 = .ok bytes) ∧
    ∀ output ∈ outputs, access m output.reference output.width 1 true = .ok ()

theorem validCall_inputs_initialized (m : Memory) (inputs outputs : List ArgumentView)
    (h : ValidCall m inputs outputs) (input : ArgumentView) (hi : input ∈ inputs) :
    ∀ i ∈ List.range input.width,
      (m.cells input.reference.allocation (input.reference.offset + i)).initialized = true := by
  obtain ⟨bytes, hread⟩ := h.2.1 input hi
  exact read_requires_initialization _ _ _ _ _ hread

theorem validCall_output_live (m : Memory) (inputs outputs : List ArgumentView)
    (h : ValidCall m inputs outputs) (output : ArgumentView) (ho : output ∈ outputs) :
    ∃ a, m.allocations output.reference.allocation = some a ∧ a.live = true ∧
      output.reference.offset + output.width ≤ a.layout.size := by
  exact access_within_allocation _ _ _ _ _ (h.2.2 output ho)

end CIL.Safety
