import CIL.Safety.ImmutableMemory

namespace CIL.Safety

theorem initialized_lookup_cells (bytes : List (BitVec 8)) :
    (List.range bytes.length).map (fun offset =>
      match bytes[offset]? with
      | some byte => (⟨byte, true⟩ : Cell)
      | none => ⟨0, false⟩) = bytes.map (fun byte => (⟨byte, true⟩ : Cell)) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp at leftBound
    simp [leftBound]

theorem staticReference_new_binding_valid (descriptor : CIL.StaticDescriptor) (m result : Memory)
    (reference : Reference)
    (missing : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) = none)
    (h : staticReference descriptor m = .ok (result, reference)) :
    StaticBindingValid result descriptor reference := by
  simp only [staticReference, missing] at h
  cases ha : allocate m ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩,
      true, [descriptor.bytes.length]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i allocated
    obtain ⟨id, memory⟩ := allocated
    cases h
    have lookup := allocation_lookup m _ id memory ha
    refine ⟨rfl, _, lookup, rfl, rfl, rfl, ?_⟩
    let initialized : Memory := { memory with
      cells := fun other offset => if other == id then
        match descriptor.bytes[offset]? with
        | some byte => ⟨byte, true⟩
        | none => ⟨0, false⟩
        else memory.cells other offset
      views := ⟨id, 0, descriptor.bytes.length, true, false⟩ :: memory.views
      staticBindings := (descriptor.identity, ⟨id, 0⟩) :: memory.staticBindings }
    change read initialized ⟨id, 0⟩ descriptor.bytes.length 1 = .ok descriptor.bytes
    have permission : (List.range descriptor.bytes.length).all (fun i =>
        permitted initialized false ⟨id, i⟩) = true := by
      apply List.all_eq_true.mpr
      intro i member
      have bound : i < descriptor.bytes.length := List.mem_range.mp member
      simp [initialized, permitted, viewContains, bound]
    have accessOK : access initialized ⟨id, 0⟩ descriptor.bytes.length 1 false = .ok () := by
      have present : initialized.allocations id = some
          ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩, true, [descriptor.bytes.length]⟩ := lookup
      have position : 0 < descriptor.bytes.length ∨ 0 = descriptor.bytes.length := by omega
      simp [access, form, liveAllocation, present, validPosition,
        nativeLimit, permission, position, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp only [read, accessOK, Bind.bind, Except.bind, Nat.zero_add]
    have cells : (List.range descriptor.bytes.length).map (fun i => initialized.cells id (0 + i)) =
        descriptor.bytes.map (fun byte => (⟨byte, true⟩ : Cell)) := by
      simpa [initialized] using initialized_lookup_cells descriptor.bytes
    simp only [Nat.zero_add] at cells
    rw [cells]
    simp [List.map_map, Function.comp_def, Pure.pure, Except.pure]

theorem staticReference_preserves_immutable (descriptor : CIL.StaticDescriptor) (m result : Memory)
    (reference : Reference) (hm : m.WellFormed)
    (h : staticReference descriptor m = .ok (result, reference)) : PreservesImmutable m result := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨key, cached⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact .refl _
  | none =>
    simp only [staticReference, hc] at h
    cases ha : allocate m ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩,
        true, [descriptor.bytes.length]⟩ <;>
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i allocated
      obtain ⟨id, memory⟩ := allocated
      cases h
      have retained := allocate_preserves_immutable _ _ _ _ hm ha
      have fresh := allocation_identity_fresh _ _ _ _ ha
      intro other a present kind
      obtain ⟨found, cells, permissions⟩ := retained other a present kind
      have different : other ≠ id := by
        rw [fresh.1]
        exact Nat.ne_of_lt (hm.1 other a present).1
      refine ⟨found, ?_, ?_⟩
      · intro offset
        simp [different, cells]
      · intro offset
        simpa [permitted, viewContains, different, Ne.symm different] using permissions offset

theorem staticReference_preserves_static_world (descriptor : CIL.StaticDescriptor)
    (descriptors : List CIL.StaticDescriptor) (m result : Memory) (reference : Reference)
    (hm : m.WellFormed) (world : StaticWorldValid descriptors m)
    (selected : descriptor ∈ descriptors)
    (h : staticReference descriptor m = .ok (result, reference)) :
    StaticWorldValid descriptors result := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨key, cached⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact world
  | none =>
    have initialized := staticReference_new_binding_valid _ _ _ _ hc h
    have retained := staticReference_preserves_immutable _ _ _ _ hm h
    simp only [staticReference, hc] at h
    cases ha : allocate m ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩,
        true, [descriptor.bytes.length]⟩ <;>
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i allocated
      obtain ⟨id, memory⟩ := allocated
      cases h
      have fresh := allocation_identity_fresh _ _ _ _ ha
      have registry : memory.staticBindings = m.staticBindings := by
        have allocation := ha
        simp only [allocate] at allocation
        repeat' first | cases allocation | split at allocation
        rfl
      refine ⟨world.1, world.2.1, ?_, ?_⟩
      · simp only [List.pairwise_cons, registry]
        refine ⟨?_, world.2.2.1⟩
        intro binding member
        constructor
        · have absent := List.find?_eq_none.mp hc binding member
          have notSame : binding.1 ≠ descriptor.identity := by
            simpa only [beq_iff_eq] using absent
          exact Ne.symm notSame
        · obtain ⟨a, present, _, _⟩ := static_registry_fields_live _ _ world binding member
          rw [fresh.1]
          exact Ne.symm (Nat.ne_of_lt (hm.1 _ _ present).1)
      · intro binding member
        simp only [List.mem_cons, registry] at member
        rcases member with rfl | member
        · exact ⟨descriptor, selected, rfl, initialized⟩
        · obtain ⟨old, oldSelected, key, valid⟩ := world.2.2.2 binding member
          exact ⟨old, oldSelected, key, retained.binding _ _ valid⟩

theorem staticReference_valid_result (descriptor : CIL.StaticDescriptor)
    (descriptors : List CIL.StaticDescriptor) (m : Memory) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m) (selected : descriptor ∈ descriptors) :
    ∃ result reference, staticReference descriptor m = .ok (result, reference) ∧
      StaticWorldValid descriptors result ∧ StaticBindingValid result descriptor reference := by
  obtain ⟨result, reference, success⟩ := staticReference_succeeds _ _ _ hm world selected
  refine ⟨result, reference, success,
    staticReference_preserves_static_world _ _ _ _ _ hm world selected success, ?_⟩
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | none => exact staticReference_new_binding_valid _ _ _ _ hc success
  | some binding =>
    obtain ⟨actual, actualSelected, key, valid⟩ :=
      world.2.2.2 binding (List.mem_of_find?_eq_some hc)
    have found : binding.1 = descriptor.identity := by
      simpa only [beq_iff_eq] using List.find?_some hc
    have same := world.2.1 actual actualSelected descriptor selected (key.trans found)
    subst actual
    obtain ⟨rfl, rfl, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc success
    exact valid

#print axioms initialized_lookup_cells
#print axioms staticReference_new_binding_valid
#print axioms staticReference_preserves_immutable
#print axioms staticReference_preserves_static_world
#print axioms staticReference_valid_result

end CIL.Safety
