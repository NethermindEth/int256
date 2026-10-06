import CIL.Safety.Memory

namespace CIL.Safety

theorem allocation_valid_iff (a : Allocation) : a.valid = true ↔ a.WellFormed := by
  simp [Allocation.valid, Allocation.WellFormed, and_assoc]

theorem liveAllocation_ok (m : Memory) (id : AllocationId) (a : Allocation)
    (h : liveAllocation m id = .ok a) : m.allocations id = some a ∧ a.live = true := by
  unfold liveAllocation at h
  cases ha : m.allocations id <;> simp only [ha] at h
  · cases h
  · split at h
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      cases h
      exact ⟨rfl, by assumption⟩
    · cases h

theorem form_preserves_provenance (m : Memory) (r result : Reference)
    (h : form m r = .ok result) : result = r := by
  simp only [form] at h
  cases ha : liveAllocation m r.allocation <;> simp [ha, Bind.bind, Except.bind, Pure.pure] at h
  split at h <;> simp_all [Except.pure]

theorem add_preserves_provenance (m : Memory) (r result : Reference) (size : Nat) (offset : BitVec 64)
    (h : add m r size offset = .ok result) : result.allocation = r.allocation := by
  simp only [add] at h
  cases ha : form m r <;> simp only [ha, Bind.bind, Except.bind] at h
  · cases h
  have he := form_preserves_provenance _ _ _ h
  subst result
  rfl

theorem formed_reference_live (m : Memory) (r result : Reference)
    (h : form m r = .ok result) :
    ∃ a, m.allocations r.allocation = some a ∧ a.live = true ∧ validPosition a r.offset = true := by
  unfold form at h
  cases ha : liveAllocation m r.allocation <;>
    simp only [ha, Bind.bind, Except.bind] at h
  · cases h
  · split at h
    · exact ⟨_, (liveAllocation_ok _ _ _ ha).1, (liveAllocation_ok _ _ _ ha).2, by assumption⟩
    · cases h

theorem access_within_allocation (m : Memory) (r : Reference) (width alignment : Nat)
    (writing : Bool) (h : access m r width alignment writing = .ok ()) :
    ∃ a, m.allocations r.allocation = some a ∧ a.live = true ∧ r.offset + width ≤ a.layout.size := by
  unfold access at h
  cases hf : form m r <;> simp only [hf, Bind.bind, Except.bind] at h
  · cases h
  · cases ha : liveAllocation m r.allocation <;> simp only [ha] at h
    · cases h
    · split at h
      · simp at h
      · simp only [Pure.pure, Except.pure] at h
        split at h
        · exact ⟨_, (liveAllocation_ok _ _ _ ha).1, (liveAllocation_ok _ _ _ ha).2, by assumption⟩
        · simp at h

theorem access_requires_permission (m : Memory) (r : Reference) (width alignment : Nat)
    (writing : Bool) (h : access m r width alignment writing = .ok ()) :
    ∀ i ∈ List.range width, permitted m writing { r with offset := r.offset + i } = true := by
  unfold access at h
  cases hf : form m r <;> simp only [hf, Bind.bind, Except.bind] at h
  · cases h
  · cases ha : liveAllocation m r.allocation <;> simp only [ha] at h
    · cases h
    · split at h
      · simp at h
      · simp only [Pure.pure, Except.pure] at h
        split at h
        · split at h
          · split at h
            · simp at h
            · split at h
              · rename_i hall
                simpa using hall
              · cases h
          · simp at h
        · simp at h

theorem expired_reference (m : Memory) (id : AllocationId) (a : Allocation)
    (h : m.allocations id = some a) (offset : Nat) :
    form (expire m id) { allocation := id, offset } = .error .expiredLifetime := by
  simp [form, liveAllocation, expire, h, Bind.bind, Except.bind]

theorem skipInit_preserves_memory (m result : Memory) (r : Reference)
    (h : skipInit m r = .ok result) : result = m := by
  simp only [skipInit] at h
  cases ha : form m r <;> simp [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  exact h.symm

theorem allocation_identity_fresh (m : Memory) (a : Allocation) (id : AllocationId) (result : Memory)
    (h : allocate m a = .ok (id, result)) : id = m.nextIdentity ∧ result.nextIdentity = m.nextIdentity + 1 := by
  simp only [allocate] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩

theorem allocation_bytes_uninitialized (m : Memory) (a : Allocation) (id : AllocationId) (result : Memory)
    (h : allocate m a = .ok (id, result)) (offset : Nat) :
    (result.cells id offset).initialized = false := by
  simp only [allocate] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      simp

theorem allocation_lookup (m : Memory) (a : Allocation) (id : AllocationId) (result : Memory)
    (h : allocate m a = .ok (id, result)) : result.allocations id = some a := by
  simp only [allocate] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      simp

theorem write_other_allocation (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment id offset : Nat) (h : write m r bytes alignment = .ok result)
    (hne : id ≠ r.allocation) : result.cells id offset = m.cells id offset := by
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    simp [hne]

theorem write_initializes (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment i : Nat) (h : write m r bytes alignment = .ok result)
    (hi : i < bytes.length) :
    result.cells r.allocation (r.offset + i) = { bits := bytes[i], initialized := true } := by
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    simp [hi]

theorem write_preserves_write_permission (m result : Memory) (r q : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat)
    (h : write m r bytes alignment = .ok result) :
    permitted result true q = permitted m true q := by
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    simp [permitted]

theorem write_read_permission (m result : Memory) (r q : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat)
    (h : write m r bytes alignment = .ok result) :
    permitted result false q =
      (decide (q.allocation = r.allocation ∧ r.offset ≤ q.offset ∧
        q.offset < r.offset + bytes.length) || permitted m false q) := by
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    simp [permitted, viewContains, eq_comm]

theorem write_preserves_wellFormed (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) (hm : m.WellFormed)
    (h : write m r bytes alignment = .ok result) : result.WellFormed := by
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    refine ⟨hm.1, ?_⟩
    intro view hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · obtain ⟨a, allocation, _, bounds⟩ := access_within_allocation _ _ _ _ _ ha
      exact ⟨a, allocation, bounds⟩
    · exact hm.2 view hv

theorem expire_preserves_wellFormed (m : Memory) (id : AllocationId)
    (hm : m.WellFormed) : (expire m id).WellFormed := by
  constructor
  · intro other a ha
    by_cases he : other = id
    · have mapped : (m.allocations other).map (fun a => { a with live := false }) = some a := by
        simpa only [expire, ite_eq_left he] using ha
      cases ho : m.allocations other
      · simp [ho] at mapped
      · rename_i old
        have original := hm.1 other old ho
        simp only [ho, Option.map_some, Option.some.injEq] at mapped
        cases mapped
        exact original
    · simp only [expire, he, ite_false] at ha
      exact hm.1 _ _ ha
  · intro view hv
    obtain ⟨a, ha, bounds⟩ := hm.2 view hv
    by_cases he : view.allocation = id
    · refine ⟨{ a with live := false }, ?_, bounds⟩
      change (if view.allocation = id then _ else _) = _
      simp only [ite_eq_left he, ha, Option.map_some]
    · exact ⟨a, by simp [expire, he, ha], bounds⟩

theorem allocate_preserves_wellFormed (m result : Memory) (a : Allocation)
    (id : AllocationId) (hm : m.WellFormed) (h : allocate m a = .ok (id, result)) :
    result.WellFormed := by
  simp only [allocate] at h
  split at h
  · cases h
  · rename_i valid
    have hav : a.WellFormed := allocation_valid_iff a |>.mp (by simpa using valid)
    split at h
    · cases h
    · cases h
      constructor
      · intro other allocation ha
        by_cases he : other = m.nextIdentity
        · simp only [he, ite_true, Option.some.injEq] at ha
          cases ha
          exact ⟨he ▸ Nat.lt_succ_self _, hav⟩
        · simp only [he, ite_false] at ha
          obtain ⟨bound, wf⟩ := hm.1 other allocation ha
          exact ⟨Nat.lt_trans bound (Nat.lt_succ_self _), wf⟩
      · intro view hv
        obtain ⟨allocation, ha, bounds⟩ := hm.2 view hv
        have ne : view.allocation ≠ m.nextIdentity := by
          have bound := (hm.1 view.allocation allocation ha).1
          exact Nat.ne_of_lt bound
        exact ⟨allocation, by simpa only [ne, ite_false] using ha, bounds⟩

theorem read_requires_initialization (m : Memory) (r : Reference) (width alignment : Nat)
    (bytes : List (BitVec 8)) (h : read m r width alignment = .ok bytes) :
    ∀ i ∈ List.range width, (m.cells r.allocation (r.offset + i)).initialized = true := by
  simp only [read] at h
  cases ha : access m r width alignment false <;>
    simp only [ha, Bind.bind, Except.bind] at h
  · cases h
  · split at h
    · rename_i hall
      simpa using hall
    · cases h

end CIL.Safety
