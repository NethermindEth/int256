import CIL.Safety.StaticMemoryLemmas
namespace CIL.Safety

/-- Loaded readonly field storage, described independently of executing a lookup. -/
def StaticBindingValid (m : Memory) (descriptor : CIL.StaticDescriptor) (reference : Reference) : Prop :=
  reference.offset = 0 ∧ ∃ allocation,
    m.allocations reference.allocation = some allocation ∧ allocation.live = true ∧
    allocation.kind = .immutableStatic ∧ allocation.layout.size = descriptor.bytes.length ∧
    read m reference descriptor.bytes.length 1 = .ok descriptor.bytes

/-- The registry contains valid fields of this extracted program. Equal keys
    describe the same field; distinct keys do not collapse storage identities. -/
def StaticWorldValid (descriptors : List CIL.StaticDescriptor) (m : Memory) : Prop :=
  (∀ descriptor ∈ descriptors, descriptor.bytes.length < nativeLimit) ∧
  (∀ left ∈ descriptors, ∀ right ∈ descriptors,
    left.identity = right.identity → left = right) ∧
  m.staticBindings.Pairwise (fun left right =>
    left.1 ≠ right.1 ∧ left.2.allocation ≠ right.2.allocation) ∧
  ∀ binding ∈ m.staticBindings, ∃ descriptor ∈ descriptors,
    descriptor.identity = binding.1 ∧ StaticBindingValid m descriptor binding.2

theorem cached_static_reference_succeeds (m : Memory) (descriptor : CIL.StaticDescriptor)
    (key : Nat) (reference : Reference)
    (cache : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) = some (key, reference))
    (valid : StaticBindingValid m descriptor reference) :
    staticReference descriptor m = .ok (m, reference) := by
  obtain ⟨offset, allocation, present, live, kind, size, bytes⟩ := valid
  simp [staticReference, cache, checkedAt, liveAllocation, present, live, kind, offset, size,
    bytes, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem wellFormed_next_unused (m : Memory) (hm : m.WellFormed) :
    m.allocations m.nextIdentity = none := by
  cases h : m.allocations m.nextIdentity with
  | none => rfl
  | some allocation =>
    have bad := (hm.1 m.nextIdentity allocation h).1
    exact False.elim (Nat.lt_irrefl _ bad)

theorem staticReference_succeeds (m : Memory) (descriptor : CIL.StaticDescriptor)
    (descriptors : List CIL.StaticDescriptor) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m) (member : descriptor ∈ descriptors) :
    ∃ result reference, staticReference descriptor m = .ok (result, reference) := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    have bindingMember : binding ∈ m.staticBindings := List.mem_of_find?_eq_some hc
    obtain ⟨actual, actualMember, key, valid⟩ := world.2.2.2 binding bindingMember
    have found : binding.1 = descriptor.identity := by
      have matched := List.find?_some hc
      simpa using matched
    have same : actual = descriptor := world.2.1 actual actualMember descriptor member (key.trans found)
    subst actual
    exact ⟨m, binding.2, cached_static_reference_succeeds _ _ _ _ hc valid⟩
  | none =>
    have unused := wellFormed_next_unused m hm
    have size := world.1 descriptor member
    have valid : (Allocation.mk .immutableStatic ⟨descriptor.bytes.length, 1, []⟩
        true [descriptor.bytes.length]).valid = true := by
      simp [Allocation.valid, size]
    simp only [staticReference, hc, allocate, valid, Bool.not_true, Bool.false_eq_true,
      ite_false, unused, Option.isSome_none, checkedAt, Except.mapError, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
    exact ⟨_, _, rfl⟩

#print axioms cached_static_reference_succeeds
#print axioms staticReference_succeeds

theorem empty_static_world_valid (descriptors : List CIL.StaticDescriptor) (m : Memory)
    (sizes : ∀ descriptor ∈ descriptors, descriptor.bytes.length < nativeLimit)
    (identities : ∀ left ∈ descriptors, ∀ right ∈ descriptors,
      left.identity = right.identity → left = right)
    (empty : m.staticBindings = []) : StaticWorldValid descriptors m := by
  refine ⟨sizes, identities, ?_, ?_⟩
  · simp [empty]
  · simp [empty]

theorem static_registry_fields_live (descriptors : List CIL.StaticDescriptor) (m : Memory)
    (world : StaticWorldValid descriptors m) (binding : Nat × Reference)
    (member : binding ∈ m.staticBindings) :
    ∃ allocation, m.allocations binding.2.allocation = some allocation ∧
      allocation.live = true ∧ allocation.kind = .immutableStatic := by
  obtain ⟨descriptor, _, _, _, allocation, present, live, kind, _, _⟩ := world.2.2.2 binding member
  exact ⟨allocation, present, live, kind⟩

#print axioms empty_static_world_valid
#print axioms static_registry_fields_live
end CIL.Safety
