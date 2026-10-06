import ProbeAudit
import CIL.Safety.Relocation

namespace CompiledSafety
open CIL.Safety

def adjacentPlacement (id : AllocationId) : Nat := 128 + 32 * id

theorem adjacent_public_placement : Placement.Valid adjacentPlacement publicMemory := by
  constructor
  · intro id a ha _
    have range := (public_memory_wellFormed.1 id a ha).1
    change id < 2 at range
    have ids : id = 0 ∨ id = 1 := by
      simpa only [Nat.lt_one_iff] using (Nat.lt_succ_iff_lt_or_eq.mp range)
    rcases ids with eq | eq <;> subst id <;>
      simp [publicMemory, memory] at ha <;> subst a <;> decide
  · intro left right a b different ha hb _ _
    have lr := (public_memory_wellFormed.1 left a ha).1
    have rr := (public_memory_wellFormed.1 right b hb).1
    change left < 2 at lr
    change right < 2 at rr
    have ls : left = 0 ∨ left = 1 := by
      simpa only [Nat.lt_one_iff] using (Nat.lt_succ_iff_lt_or_eq.mp lr)
    have rs : right = 0 ∨ right = 1 := by
      simpa only [Nat.lt_one_iff] using (Nat.lt_succ_iff_lt_or_eq.mp rr)
    rcases ls with eq | eq <;> subst left <;>
      rcases rs with eq | eq <;> subst right
    all_goals try exact False.elim (different rfl)
    all_goals
      simp [publicMemory, memory] at ha hb
      subst a
      subst b
      decide

theorem adjacent_boundary_same_address :
    concreteAddress adjacentPlacement ⟨0, 32⟩ =
      concreteAddress adjacentPlacement ⟨1, 0⟩ := by rfl

/-- The neighbour is live and its output view permits this access. A source
reference at the same numerical address does not acquire that provenance. -/
theorem adjacent_access_distinguished :
    access publicMemory ⟨1, 0⟩ 8 1 false = .ok () ∧
    access publicMemory ⟨0, 32⟩ 8 1 false = .error .outsideAllocation := ⟨rfl, rfl⟩

#print axioms adjacent_public_placement
#print axioms adjacent_boundary_same_address
#print axioms adjacent_access_distinguished
/-- The compiled public entry fails for every fuel even though a legal physical
placement puts an accessible neighbouring allocation at the attempted address. -/
theorem adjacent_compiled_counterexample :
    Placement.Valid adjacentPlacement publicMemory ∧
    concreteAddress adjacentPlacement ⟨0, 32⟩ = concreteAddress adjacentPlacement ⟨1, 0⟩ ∧
    (ValidCall publicMemory [⟨⟨0, 0⟩, 32⟩, ⟨⟨0, 0⟩, 32⟩] [⟨⟨1, 0⟩, 32⟩] ∧
      StaticWorldValid (programStaticDescriptors Extracted.program) publicMemory) ∧
    ∀ fuel result,
      invoke Extracted.program fuel Extracted.entryIndex publicArguments publicMemory ≠ .ok result := by
  exact ⟨adjacent_public_placement, adjacent_boundary_same_address, public_counterexample⟩

#print axioms adjacent_compiled_counterexample
def resultOnlyMemory : CIL.Memory := fun address =>
  match address with
  | .byte offset => some (.i8 (if offset = 136 then 1 else 0))
  | _ => none

@[irreducible] def resultObservation (result : CIL.Memory × List CIL.Value) :=
  (CIL.readBytes result.1 160 32, result.2.isEmpty)

theorem result_only_same_bytes :
    (∀ id : Fin 2, ∀ offset : Fin 32,
      resultOnlyMemory (.byte (adjacentPlacement id.val + offset.val)) =
        some (.i8 (publicMemory.cells id.val offset.val).bits)) ∧
    CIL.readBytes resultOnlyMemory 128 32 = some (2^64) := by decide +kernel

/-- The allocation-free interpreter returns the correct initial-input sum for
    this same compiled entry and physical placement, despite its discarded
    out-of-allocation read. This is a concrete witness, not a universal contract. -/
theorem result_only_observation :
    (CIL.invoke Extracted.program 256 Extracted.entryIndex
      [.object 128, .object 128, .object 160] resultOnlyMemory).map
        resultObservation =
      some (some ((2^64 + 2^64) % 2^256), true) := by decide +kernel

#print axioms result_only_same_bytes
#print axioms result_only_observation
end CompiledSafety
