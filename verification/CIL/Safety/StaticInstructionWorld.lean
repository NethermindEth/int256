import CIL.Safety.StaticInitialization

namespace CIL.Safety

theorem write_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat)
    (world : StaticWorldValid descriptors m) (h : write m r bytes alignment = .ok result) :
    StaticWorldValid descriptors result := by
  apply (write_preserves_immutable _ _ _ _ _ h).world descriptors world
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    rfl

theorem checked_write_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat)
    (reference : ManagedReference) (width : Nat) (world : StaticWorldValid descriptors m)
    (h : checkedAt reference width (write m r bytes alignment) = .ok result) :
    StaticWorldValid descriptors result := by
  cases hw : write m r bytes alignment <;> simp only [hw, checkedAt, Except.mapError] at h
  · cases h
  · cases h
    exact write_preserves_static_world _ _ _ _ _ _ world hw

theorem storeValue_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (reference : ManagedReference) (value : CIL.Value)
    (world : StaticWorldValid descriptors m) (h : storeValue m reference value = .ok result) :
    StaticWorldValid descriptors result := by
  unfold storeValue at h
  split at h <;> try cases h
  all_goals
    cases reference with
    | null => cases h
    | address address =>
      simp only [referenceAt, Bind.bind, Except.bind] at h
      exact checked_write_preserves_static_world _ _ _ _ _ _ _ _ world h

theorem memoryInstruction_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (operation : CIL.MemoryOp) (stack values : List Value) (m result : Memory)
    (world : StaticWorldValid descriptors m)
    (h : memoryInstruction operation stack m = .ok (result, values)) :
    StaticWorldValid descriptors result := by
  unfold memoryInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact world
      | solve | apply storeValue_preserves_static_world _ _ _ _ _ world; assumption
      | cases h
      | split at h

theorem instruction_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (operation : CIL.Op) (stack values : List Value) (m result : Memory)
    (world : StaticWorldValid descriptors m)
    (h : instruction operation stack m = .ok (result, values)) :
    StaticWorldValid descriptors result := by
  unfold instruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact world
      | solve | apply memoryInstruction_preserves_static_world _ _ _ _ _ _ world; assumption
      | solve | apply storeValue_preserves_static_world _ _ _ _ _ world; assumption
      | cases h
      | split at h

/-- Every site descriptor belongs to the selected extracted program's static
    world. Selection is independent of executing or proving a lookup. -/
def StaticSitesValid (descriptors : List CIL.StaticDescriptor) (body : CIL.Method) : Prop :=
  ∀ site ∈ body.staticSites, site.2 ∈ descriptors

theorem selected_static_site (descriptors : List CIL.StaticDescriptor) (body : CIL.Method)
    (pc site : Nat) (descriptor : CIL.StaticDescriptor) (sites : StaticSitesValid descriptors body)
    (found : body.staticSites.find? (fun site => site.1 == pc) = some (site, descriptor)) :
    descriptor ∈ descriptors := sites _ (List.mem_of_find?_eq_some found)

theorem staticInstruction_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory) (hm : m.WellFormed)
    (sites : StaticSitesValid descriptors body) (world : StaticWorldValid descriptors m)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    StaticWorldValid descriptors result := by
  unfold staticInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact world
      | solve | apply memoryInstruction_preserves_static_world _ _ _ _ _ _ world; assumption
      | solve |
          apply staticReference_preserves_static_world
          · exact hm
          · exact world
          · apply selected_static_site _ _ _ _ _ sites; assumption
          · assumption
      | cases h
      | split at h

#print axioms write_preserves_static_world
#print axioms memoryInstruction_preserves_static_world
#print axioms instruction_preserves_static_world
#print axioms staticInstruction_preserves_static_world

end CIL.Safety
