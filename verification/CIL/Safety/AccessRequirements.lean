import CIL.Safety.Calling

namespace CIL.Safety

/-- Ordinary storage requirements for one access. This contains no instruction,
    method body, future execution or successful-check hypothesis. -/
structure AccessRequirements (m : Memory) (r : Reference) (width alignment : Nat)
    (writing : Bool) (allocation : Allocation) : Prop where
  present : m.allocations r.allocation = some allocation
  live : allocation.live = true
  position : validPosition allocation r.offset = true
  layout : ∀ slot ∈ allocation.layout.referenceSlots,
    ¬ (r.offset < slot.1 + slot.2 ∧ slot.1 < r.offset + width)
  extent : r.offset + width ≤ allocation.layout.size
  aligned : 0 < alignment ∧ allocation.layout.alignment % alignment = 0 ∧ r.offset % alignment = 0
  mutable : writing = true → allocation.kind ≠ .immutableStatic
  permission : ∀ i < width, permitted m writing { r with offset := r.offset + i } = true

theorem permitted_by_view {m : Memory} {r : Reference} {writing : Bool} {view : View}
    (member : view ∈ m.views) (same : view.allocation = r.allocation)
    (start : view.start ≤ r.offset) (finish : r.offset < view.start + view.length)
    (authority : (if writing then view.writable else view.readable) = true) :
    permitted m writing r = true := by
  apply List.any_eq_true.mpr
  refine ⟨view, member, ?_⟩
  simp [viewContains, same, start, finish, authority]

theorem AccessRequirements.access {m : Memory} {r : Reference} {width alignment : Nat}
    {writing : Bool} {allocation : Allocation}
    (ready : AccessRequirements m r width alignment writing allocation) :
    access m r width alignment writing = .ok () := by
  have slots : allocation.layout.referenceSlots.any (fun slot =>
      decide (r.offset < slot.1 + slot.2 ∧ slot.1 < r.offset + width)) = false := by
    simpa only [List.any_eq_false, decide_eq_true_eq] using ready.layout
  have permitted : (List.range width).all (fun i =>
      permitted m writing { r with offset := r.offset + i }) = true := by
    apply List.all_eq_true.mpr
    intro i member
    exact ready.permission i (List.mem_range.mp member)
  have immutable : (writing && (allocation.kind == .immutableStatic)) = false := by
    cases h : writing
    · rfl
    · simp [ready.mutable h]
  simp only [CIL.Safety.access, form, liveAllocation, ready.present, ready.live, ready.position,
    slots, ready.extent, ready.aligned.1, ready.aligned.2.1, ready.aligned.2.2,
    immutable, permitted, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Bool.false_eq_true, decide_true, ite_true, ite_false]
  rfl

theorem read_snapshot {m : Memory} {r : Reference} {width alignment : Nat}
    {allocation : Allocation} (ready : AccessRequirements m r width alignment false allocation)
    (initialized : ∀ i < width, (m.cells r.allocation (r.offset + i)).initialized = true) :
    read m r width alignment =
      .ok ((List.range width).map fun i => (m.cells r.allocation (r.offset + i)).bits) := by
  have cells : ((List.range width).map fun i =>
      m.cells r.allocation (r.offset + i)).all (·.initialized) = true := by
    simp only [List.all_map, List.all_eq_true]
    intro i member
    exact initialized i (List.mem_range.mp member)
  simp [read, ready.access, cells, List.map_map, Function.comp_def,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem read_result_snapshot {m : Memory} {r : Reference} {width alignment : Nat}
    {bytes : List (BitVec 8)} (h : read m r width alignment = .ok bytes) :
    bytes = (List.range width).map (fun i => (m.cells r.allocation (r.offset + i)).bits) := by
  unfold read at h
  cases ha : access m r width alignment false <;>
    simp only [ha, Bind.bind, Except.bind] at h
  · cases h
  · split at h
    · simpa [Pure.pure, Except.pure, List.map_map, Function.comp_def] using h.symm
    · cases h

#print axioms AccessRequirements.access
#print axioms read_snapshot
#print axioms read_result_snapshot
#print axioms permitted_by_view

end CIL.Safety
