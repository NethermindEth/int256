import CIL.Safety.AccessSlices

namespace CIL.Safety

theorem write_succeeds {m : Memory} {r : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (ready : access m r bytes.length alignment true = .ok ()) :
    ∃ result, write m r bytes alignment = .ok result := by
  simp only [write, ready, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨_, rfl⟩

theorem write_allocations (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment : Nat) (h : write m r bytes alignment = .ok result) :
    result.allocations = m.allocations := by
  unfold write at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h; rfl

theorem write_outside (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment id offset : Nat) (h : write m r bytes alignment = .ok result)
    (outside : id ≠ r.allocation ∨ offset < r.offset ∨ r.offset + bytes.length ≤ offset) :
    result.cells id offset = m.cells id offset := by
  unfold write at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    rcases outside with different | before | after
    · simp [different]
    · simp [show ¬ r.offset ≤ offset by omega]
    · have bound : bytes.length ≤ offset - r.offset := by omega
      simp [List.getElem?_eq_none_iff.mpr bound]

theorem write_preserves_initialization (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment id offset : Nat) (h : write m r bytes alignment = .ok result)
    (initialized : (m.cells id offset).initialized = true) :
    (result.cells id offset).initialized = true := by
  by_cases inside : id = r.allocation ∧ r.offset ≤ offset ∧ offset < r.offset + bytes.length
  · obtain ⟨rfl, start, finish⟩ := inside
    have index : offset - r.offset < bytes.length := by omega
    have written := write_initializes _ _ _ _ _ _ h index
    have same : r.offset + (offset - r.offset) = offset := by omega
    rw [same] at written
    rw [written]
  · have outside : id ≠ r.allocation ∨ offset < r.offset ∨ r.offset + bytes.length ≤ offset := by omega
    rw [write_outside _ _ _ _ _ _ _ h outside]
    exact initialized

theorem AccessRequirements.after_write {m result : Memory} {r q : Reference}
    {bytes : List (BitVec 8)} {writeAlignment width alignment : Nat} {writing : Bool} {allocation : Allocation}
    (ready : AccessRequirements m q width alignment writing allocation)
    (h : write m r bytes writeAlignment = .ok result) :
    AccessRequirements result q width alignment writing allocation := by
  refine ⟨?_, ready.live, ready.position, ready.layout, ready.extent, ready.aligned, ready.mutable, ?_⟩
  · rw [write_allocations _ _ _ _ _ h]
    exact ready.present
  · intro i bound
    cases writing
    · rw [write_read_permission _ _ _ _ _ _ h, ready.permission i bound]
      simp
    · rw [write_preserves_write_permission _ _ _ _ _ _ h]
      exact ready.permission i bound

theorem write_preserves_readability {m result : Memory} {r q : Reference}
    {bytes old : List (BitVec 8)} {writeAlignment width alignment : Nat}
    (h : write m r bytes writeAlignment = .ok result)
    (readable : read m q width alignment = .ok old) :
    ∃ current, read result q width alignment = .ok current := by
  have accessOK : access m q width alignment false = .ok () := by
    unfold read at readable
    cases ha : access m q width alignment false with
    | error fault => simp [ha, Bind.bind, Except.bind] at readable
    | ok value => cases value; rfl
  obtain ⟨allocation, ready⟩ := access_requirements accessOK
  refine ⟨_, read_snapshot (ready.after_write h) ?_⟩
  intro i bound
  exact write_preserves_initialization _ _ _ _ _ _ _ h
    (read_requires_initialization _ _ _ _ _ readable i (List.mem_range.mpr bound))

/-- A disjoint write retains the exact readable snapshot, including when both
    intervals belong to the same allocation. -/
theorem write_preserves_disjoint_read {m result : Memory} {r q : Reference}
    {bytes old : List (BitVec 8)} {writeAlignment width alignment : Nat}
    (h : write m r bytes writeAlignment = .ok result)
    (readable : read m q width alignment = .ok old)
    (disjoint : q.allocation ≠ r.allocation ∨
      q.offset + width ≤ r.offset ∨ r.offset + bytes.length ≤ q.offset) :
    read result q width alignment = .ok old := by
  obtain ⟨current, reading⟩ := write_preserves_readability h readable
  have same : current = old := by
    rw [read_result_snapshot reading, read_result_snapshot readable]
    apply List.map_congr_left
    intro i member
    have bound := List.mem_range.mp member
    have outside : q.allocation ≠ r.allocation ∨ q.offset + i < r.offset ∨
        r.offset + bytes.length ≤ q.offset + i := by
      rcases disjoint with different | before | after
      · exact Or.inl different
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    rw [write_outside _ _ _ _ _ q.allocation (q.offset + i) h outside]
  simpa only [same] using reading

theorem write_readback (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment : Nat) (h : write m r bytes alignment = .ok result) :
    read result r bytes.length alignment = .ok bytes := by
  have accessOK : access m r bytes.length alignment true = .ok () := by
    unfold write at h
    cases ha : access m r bytes.length alignment true with
    | error fault => simp [ha, Bind.bind, Except.bind] at h
    | ok value => cases value; rfl
  obtain ⟨allocation, ready⟩ := access_requirements accessOK
  have canRead : AccessRequirements result r bytes.length alignment false allocation := by
    refine ⟨?_, ready.live, ready.position, ready.layout, ready.extent, ready.aligned, by simp, ?_⟩
    · rw [write_allocations _ _ _ _ _ h]
      exact ready.present
    · intro i bound
      rw [write_read_permission _ _ _ _ _ _ h]
      simp [show r.offset ≤ r.offset + i by omega, show r.offset + i < r.offset + bytes.length by omega]
  have snapshot := read_snapshot canRead (fun i bound => by
    rw [write_initializes _ _ _ _ _ _ h bound])
  have same : (List.range bytes.length).map (fun i => (result.cells r.allocation (r.offset + i)).bits) = bytes := by
    apply List.ext_getElem
    · simp
    · intro i left right
      simp only [List.getElem_map, List.getElem_range]
      rw [write_initializes _ _ _ _ _ _ h right]
  rw [same] at snapshot
  exact snapshot

#print axioms write_outside
#print axioms write_preserves_initialization
#print axioms AccessRequirements.after_write
#print axioms write_preserves_readability
#print axioms write_readback
#print axioms write_preserves_disjoint_read

end CIL.Safety
