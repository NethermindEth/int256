import CIL.Safety.MemoryLemmas

namespace CIL.Safety

/-- Allocation creates fresh identities; writes leave all existing allocation
    metadata and lifetime tokens intact. Expiration is accounted for separately. -/
structure AllocationExtension (before after : Memory) : Prop where
  next : before.nextIdentity ≤ after.nextIdentity
  lookup : ∀ id, id < before.nextIdentity → after.allocations id = before.allocations id

theorem AllocationExtension.refl (m : Memory) : AllocationExtension m m :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem AllocationExtension.trans {first middle last : Memory}
    (left : AllocationExtension first middle) (right : AllocationExtension middle last) :
    AllocationExtension first last := by
  refine ⟨Nat.le_trans left.next right.next, ?_⟩
  intro id bound
  rw [right.lookup id (Nat.lt_of_lt_of_le bound left.next), left.lookup id bound]

theorem allocate_extends_allocations (m result : Memory) (a : Allocation) (id : AllocationId)
    (h : allocate m a = .ok (id, result)) : AllocationExtension m result := by
  simp only [allocate] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      refine ⟨Nat.le_succ _, ?_⟩
      intro other bound
      simp [Nat.ne_of_lt bound]

theorem write_extends_allocations (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment : Nat) (h : write m r bytes alignment = .ok result) :
    AllocationExtension m result := by
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem expire_preserves_older_allocations (m : Memory) (id watermark : AllocationId)
    (fresh : watermark ≤ id) (other : AllocationId) (old : other < watermark) :
    (expire m id).allocations other = m.allocations other := by
  have ne : other ≠ id := Nat.ne_of_lt (Nat.lt_of_lt_of_le old fresh)
  simp [expire, ne]

theorem form_allocation_congr (m result : Memory) (r : Reference)
    (same : result.allocations r.allocation = m.allocations r.allocation) :
    form result r = form m r := by
  simp only [form, liveAllocation, same]

theorem AllocationExtension.preserves_reference {m result : Memory} (ext : AllocationExtension m result)
    (hm : m.WellFormed) (r formed : Reference) (h : form m r = .ok formed) :
    form result r = .ok formed := by
  obtain ⟨a, present, _, _⟩ := formed_reference_live _ _ _ h
  rw [form_allocation_congr _ _ _ (ext.lookup r.allocation (hm.1 _ _ present).1)]
  exact h

theorem read_allocation_congr (m result : Memory) (r : Reference) (width alignment : Nat)
    (same : result.allocations r.allocation = m.allocations r.allocation)
    (cells : result.cells = m.cells) (views : result.views = m.views) :
    read result r width alignment = read m r width alignment := by
  simp only [read, access, form, liveAllocation, permitted, same, cells, views]
  rfl

end CIL.Safety
