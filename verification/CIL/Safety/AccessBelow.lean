import CIL.Safety.MemoryBelow
import CIL.Safety.WriteEffects

namespace CIL.Safety

/-- Retains old allocation validity, existing authority and initialization;
    authorized writes may change the byte values. -/
structure AccessBelow (watermark : Nat) (before after : Memory) : Prop where
  allocations : ∀ id, id < watermark → after.allocations id = before.allocations id
  permissions : ∀ id, id < watermark → ∀ offset writing,
    permitted before writing ⟨id, offset⟩ = true → permitted after writing ⟨id, offset⟩ = true
  initialized : ∀ id, id < watermark → ∀ offset,
    (before.cells id offset).initialized = true → (after.cells id offset).initialized = true

theorem MemoryBelow.accessBelow {watermark : Nat} {before after : Memory}
    (h : MemoryBelow watermark before after) : AccessBelow watermark before after :=
  ⟨h.allocations, fun id old offset writing allowed => by rw [h.permissions id old offset writing]; exact allowed,
    fun id old offset initialized => by rw [h.cells id old offset]; exact initialized⟩

theorem AccessBelow.trans {watermark : Nat} {first middle last : Memory}
    (left : AccessBelow watermark first middle) (right : AccessBelow watermark middle last) :
    AccessBelow watermark first last :=
  ⟨fun id old => (right.allocations id old).trans (left.allocations id old),
    fun id old offset writing allowed => right.permissions id old offset writing (left.permissions id old offset writing allowed),
    fun id old offset initialized => right.initialized id old offset (left.initialized id old offset initialized)⟩

theorem AccessBelow.weaken {lower upper : Nat} {before after : Memory}
    (h : AccessBelow upper before after) (bound : lower ≤ upper) : AccessBelow lower before after :=
  ⟨fun id old => h.allocations id (Nat.lt_of_lt_of_le old bound),
    fun id old => h.permissions id (Nat.lt_of_lt_of_le old bound),
    fun id old => h.initialized id (Nat.lt_of_lt_of_le old bound)⟩

theorem write_preserves_access_below {memory result : Memory} {reference : Reference}
    {bytes : List (BitVec 8)} {alignment : Nat}
    (written : write memory reference bytes alignment = .ok result) (watermark : Nat) :
    AccessBelow watermark memory result := by
  refine ⟨fun id _ => congrFun (write_allocations _ _ _ _ _ written) id, ?_, ?_⟩
  · intro id _ offset writing allowed
    cases writing
    · rw [write_read_permission _ _ _ _ _ _ written, allowed]; simp
    · rw [write_preserves_write_permission _ _ _ _ _ _ written]; exact allowed
  · intro id _ offset initialized
    exact write_preserves_initialization _ _ _ _ _ _ _ written initialized

theorem AccessBelow.requirements {watermark : Nat} {memory result : Memory}
    (retained : AccessBelow watermark memory result) {reference : Reference}
    {width alignment : Nat} {writing : Bool} {allocation : Allocation}
    (ready : AccessRequirements memory reference width alignment writing allocation)
    (old : reference.allocation < watermark) :
    AccessRequirements result reference width alignment writing allocation := by
  refine ⟨?_, ready.live, ready.position, ready.layout, ready.extent, ready.aligned, ready.mutable, ?_⟩
  · rw [retained.allocations reference.allocation old]; exact ready.present
  · intro i bound
    exact retained.permissions reference.allocation old (reference.offset + i) writing (ready.permission i bound)

theorem AccessBelow.access {watermark : Nat} {memory result : Memory}
    (retained : AccessBelow watermark memory result) {reference : Reference}
    {width alignment : Nat} {writing : Bool}
    (ready : CIL.Safety.access memory reference width alignment writing = .ok ())
    (old : reference.allocation < watermark) :
    CIL.Safety.access result reference width alignment writing = .ok () := by
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  exact (retained.requirements requirements old).access

theorem AccessBelow.readable {watermark : Nat} {memory result : Memory}
    (retained : AccessBelow watermark memory result) {reference : Reference}
    {width alignment : Nat} {bytes : List (BitVec 8)}
    (loaded : read memory reference width alignment = .ok bytes)
    (old : reference.allocation < watermark) :
    ∃ current, read result reference width alignment = .ok current := by
  have ready : CIL.Safety.access memory reference width alignment false = .ok () := by
    unfold read at loaded
    cases h : CIL.Safety.access memory reference width alignment false with
    | error fault => simp [h, Bind.bind, Except.bind] at loaded
    | ok value => cases value; rfl
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  refine ⟨_, read_snapshot (retained.requirements requirements old) ?_⟩
  intro i bound
  exact retained.initialized reference.allocation old (reference.offset + i)
    (read_requires_initialization _ _ _ _ _ loaded i (List.mem_range.mpr bound))


/-- Unchanged cells plus retained authority preserve the exact read result. -/
theorem AccessBelow.read_eq {watermark : Nat} {memory result : Memory}
    (retained : AccessBelow watermark memory result) {reference : Reference}
    {width alignment : Nat} {bytes : List (BitVec 8)}
    (loaded : read memory reference width alignment = .ok bytes)
    (old : reference.allocation < watermark)
    (unchanged : ∀ i < width, result.cells reference.allocation (reference.offset + i) =
      memory.cells reference.allocation (reference.offset + i)) :
    read result reference width alignment = .ok bytes := by
  obtain ⟨current, reading⟩ := retained.readable loaded old
  have same : current = bytes := by
    rw [read_result_snapshot reading, read_result_snapshot loaded]
    apply List.map_congr_left
    intro i member
    rw [unchanged i (List.mem_range.mp member)]
  simpa only [same] using reading

#print axioms MemoryBelow.accessBelow
#print axioms AccessBelow.trans
#print axioms AccessBelow.weaken
#print axioms write_preserves_access_below
#print axioms AccessBelow.requirements
#print axioms AccessBelow.access
#print axioms AccessBelow.readable
#print axioms AccessBelow.read_eq

end CIL.Safety
