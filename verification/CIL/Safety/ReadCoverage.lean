import CIL.Safety.AccessSlices

namespace CIL.Safety

/-- Full-range layout and extent checks plus initialized readable slices justify
    a full read. Every byte must be covered; write permission alone is insufficient. -/
theorem read_of_cover {memory : Memory} {reference : Reference} {width : Nat}
    {allocation : Allocation}
    (ready : AccessRequirements memory reference width 1 true allocation)
    (cover : ∀ i < width, ∃ start count bytes,
      start ≤ i ∧ i < start + count ∧
      read memory { reference with offset := reference.offset + start } count 1 = .ok bytes) :
    read memory reference width 1 =
      .ok ((List.range width).map fun i => (memory.cells reference.allocation (reference.offset + i)).bits) := by
  have covered (i : Nat) (bound : i < width) :
      permitted memory false { reference with offset := reference.offset + i } = true ∧
      (memory.cells reference.allocation (reference.offset + i)).initialized = true := by
    obtain ⟨start, count, bytes, lower, upper, loaded⟩ := cover i bound
    have accessOK : access memory { reference with offset := reference.offset + start } count 1 false = .ok () := by
      unfold read at loaded
      cases h : access memory { reference with offset := reference.offset + start } count 1 false with
      | error fault => simp [h, Bind.bind, Except.bind] at loaded
      | ok value => cases value; rfl
    obtain ⟨_, slice⟩ := access_requirements accessOK
    have offset : reference.offset + start + (i - start) = reference.offset + i := by omega
    have permission := slice.permission (i - start) (by omega)
    have initialized := read_requires_initialization _ _ _ _ _ loaded (i - start) (by simp; omega)
    exact ⟨by simpa only [offset] using permission, by simpa only [offset] using initialized⟩
  apply read_snapshot (allocation := allocation)
  · exact { ready with mutable := by simp, permission := fun i bound => (covered i bound).1 }
  · exact fun i bound => (covered i bound).2

#print axioms read_of_cover

end CIL.Safety
