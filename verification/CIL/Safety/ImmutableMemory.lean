import CIL.Safety.AllocationExtension
import CIL.Safety.StaticWorld

namespace CIL.Safety

/-- Existing immutable storage retains its allocation, contents, initialization
    and read permissions. Newly loaded fields are accounted for separately. -/
def PreservesImmutable (before after : Memory) : Prop :=
  ∀ id a, before.allocations id = some a → a.kind = .immutableStatic →
    after.allocations id = some a ∧
      (∀ offset, after.cells id offset = before.cells id offset) ∧
      ∀ offset, permitted after false ⟨id, offset⟩ = permitted before false ⟨id, offset⟩

theorem PreservesImmutable.refl (m : Memory) : PreservesImmutable m m :=
  fun _ _ present _ => ⟨present, fun _ => rfl, fun _ => rfl⟩

theorem PreservesImmutable.trans {first middle last : Memory}
    (left : PreservesImmutable first middle) (right : PreservesImmutable middle last) :
    PreservesImmutable first last := by
  intro id a present kind
  obtain ⟨found, cells, permissions⟩ := left id a present kind
  obtain ⟨final, finalCells, finalPermissions⟩ := right id a found kind
  exact ⟨final, fun offset => (finalCells offset).trans (cells offset),
    fun offset => (finalPermissions offset).trans (permissions offset)⟩

theorem PreservesImmutable.read {m result : Memory} (preserves : PreservesImmutable m result)
    (r : Reference) (a : Allocation) (present : m.allocations r.allocation = some a)
    (kind : a.kind = .immutableStatic) (width alignment : Nat) :
    read result r width alignment = read m r width alignment := by
  obtain ⟨found, cells, permissions⟩ := preserves _ _ present kind
  simp only [CIL.Safety.read, CIL.Safety.access, CIL.Safety.form, CIL.Safety.liveAllocation, found, present]
  simp only [cells, permissions]

theorem PreservesImmutable.binding {m result : Memory} (preserves : PreservesImmutable m result)
    (descriptor : CIL.StaticDescriptor) (reference : Reference)
    (valid : StaticBindingValid m descriptor reference) :
    StaticBindingValid result descriptor reference := by
  obtain ⟨offset, a, present, live, kind, size, bytes⟩ := valid
  exact ⟨offset, a, (preserves _ _ present kind).1, live, kind, size,
    (preserves.read reference a present kind _ _).trans bytes⟩

theorem PreservesImmutable.world {m result : Memory} (preserves : PreservesImmutable m result)
    (descriptors : List CIL.StaticDescriptor) (world : StaticWorldValid descriptors m)
    (registry : result.staticBindings = m.staticBindings) : StaticWorldValid descriptors result := by
  refine ⟨world.1, world.2.1, ?_, ?_⟩
  · rw [registry]
    exact world.2.2.1
  · intro binding member
    rw [registry] at member
    obtain ⟨descriptor, selected, key, valid⟩ := world.2.2.2 binding member
    exact ⟨descriptor, selected, key, preserves.binding _ _ valid⟩

theorem write_preserves_immutable (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat)
    (h : write m r bytes alignment = .ok result) : PreservesImmutable m result := by
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    intro id a present kind
    have different : r.allocation ≠ id := by
      intro equal
      cases live : a.live <;> cases position : validPosition a r.offset <;>
        simp [access, form, liveAllocation, equal, present, kind, live, position,
          Bind.bind, Except.bind, Pure.pure, Except.pure] at ha
      repeat' first | cases ha | split at ha
    refine ⟨present, ?_, ?_⟩
    · intro offset
      simp [Ne.symm different]
    · intro offset
      simp [permitted, viewContains, different]

theorem allocate_preserves_immutable (m result : Memory) (a : Allocation) (id : AllocationId)
    (hm : m.WellFormed) (h : allocate m a = .ok (id, result)) : PreservesImmutable m result := by
  simp only [allocate] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      intro other old present kind
      have different := Nat.ne_of_lt (hm.1 other old present).1
      exact ⟨by simp [different, present], by simp [different], fun _ => rfl⟩

#print axioms write_preserves_immutable
#print axioms allocate_preserves_immutable
#print axioms PreservesImmutable.binding
#print axioms PreservesImmutable.world

end CIL.Safety
