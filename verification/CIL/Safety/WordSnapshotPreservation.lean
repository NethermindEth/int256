import CIL.Safety.WordSnapshots

namespace CIL.Safety

/-- A store into another typed private home cannot change any remembered word.
    Distinct local kinds exclude the same slot; allocation ordering then proves
    disjointness. This does not grant readability to the newly written home. -/
theorem WordSnapshots.after_other_kind_write {entered before after : Memory} {boundary : Nat}
    {kinds slots} {known : Nat → Option (BitVec 64)} {bytes : List (BitVec 8)} {alignment : Nat}
    (snapshots : WordSnapshots before slots known)
    (homes : WritableHomes entered boundary kinds slots)
    (index : Nat) (kind : CIL.LocalKind) (reference : Reference)
    (differentKind : kind ≠ .word64)
    (slot : slots[index]? = some (.bytes kind reference))
    (written : write before reference bytes alignment = .ok after) :
    WordSnapshots after slots known := by
  intro other value present
  obtain ⟨word, wordSlot, readable⟩ := snapshots other value present
  have different : other ≠ index := by
    intro same
    subst other
    rw [slot] at wordSlot
    cases wordSlot
    exact differentKind rfl
  exact ⟨word, wordSlot, write_preserves_disjoint_read written readable
    (Or.inl (homes.distinct other index .word64 kind word reference different wordSlot slot))⟩

#print axioms WordSnapshots.after_other_kind_write
end CIL.Safety
