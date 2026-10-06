import CIL.Safety.StaticInstructionWorld
import CIL.Safety.FrameSetupLemmas

namespace CIL.Safety

theorem allocateHome_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation width : Nat) (r : Reference) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m)
    (h : allocateHome m activation width = .ok (r, result)) : StaticWorldValid descriptors result := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, 1, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    have retained := allocate_preserves_immutable _ _ _ _ hm ha
    have allocationWorld : StaticWorldValid descriptors memory := by
      apply retained.world descriptors world
      have success := ha
      simp only [allocate] at success
      repeat' first | cases success | split at success
      rfl
    refine PreservesImmutable.world (m := memory)
      (result := { memory with views := ⟨id, 0, width, true, true⟩ :: memory.views })
      ?_ descriptors allocationWorld rfl
    intro other a present kind
    have different : other ≠ id := by
      have lookup := allocation_lookup m _ id memory ha
      intro same
      subst other
      have equal := Option.some.inj (present.symm.trans lookup)
      subst a
      cases kind
    refine ⟨present, fun _ => rfl, ?_⟩
    intro offset
    simp [permitted, viewContains, Ne.symm different]

theorem storeLocal_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (slot final : LocalSlot) (value : Value)
    (world : StaticWorldValid descriptors m)
    (h : storeLocal m slot value = .ok (final, result)) : StaticWorldValid descriptors result := by
  unfold storeLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact world
      | solve | apply checked_write_preserves_static_world _ _ _ _ _ _ _ _ world; assumption
      | cases h
      | split at h

theorem makeLocal_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation : Nat) (kind : CIL.LocalKind) (initial : CIL.Value)
    (slot : LocalSlot) (owned : List AllocationId) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    StaticWorldValid descriptors result := by
  unfold makeLocal at h
  split at h
  · split at h
    · cases h; exact world
    · cases h; exact world
    · cases h
  all_goals
    cases ha : allocateHome m activation (localWidth kind) <;>
      simp only [ha, Bind.bind, Except.bind] at h
    · cases h
    · rename_i home
      obtain ⟨reference, memory⟩ := home
      have updated := allocateHome_preserves_static_world _ _ _ _ _ _ hm world ha
      split at h
      · simp only [Pure.pure, Except.pure] at h
        cases h
        exact updated
      · cases hs : storeLocal memory (.bytes kind reference) (.scalar initial) <;>
          simp only [hs, Pure.pure, Except.pure] at h
        · cases h
        · rename_i stored
          obtain ⟨slot', memory'⟩ := stored
          cases h
          exact storeLocal_preserves_static_world _ _ _ _ _ _ updated hs

theorem makeLocals_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (hm : m.WellFormed) (world : StaticWorldValid descriptors m)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    StaticWorldValid descriptors result := by
  induction kinds generalizing initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; exact world
    · cases h
  | cons kind kinds ih =>
    cases initializers with
    | nil => cases h
    | cons initial initials =>
      simp only [makeLocals] at h
      cases hl : makeLocal activation kind initial m <;>
        simp only [hl, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨slot, ids, memory⟩ := home
        have hw := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ hm hl
        have updated := makeLocal_preserves_static_world _ _ _ _ _ _ _ _ hm world hl
        cases hr : makeLocals activation kinds initials memory <;>
          simp only [hr, Pure.pure, Except.pure] at h
        · cases h
        · rename_i rest
          obtain ⟨rest, other, final⟩ := rest
          cases h
          exact ih memory final initials rest other hw updated hr

theorem makeArgumentHomes_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation : Nat) (indices : List Nat) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    StaticWorldValid descriptors result := by
  induction indices generalizing m homes owned result with
  | nil => cases h; exact world
  | cons index indices ih =>
    simp only [makeArgumentHomes] at h
    split at h
    · rename_i bits hv
      cases ha : allocateHome m activation (localWidth .vector256) <;>
        simp only [ha, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨reference, memory⟩ := home
        have hw := allocateHome_preserves_wellFormed _ _ _ _ _ hm ha
        have updated := allocateHome_preserves_static_world _ _ _ _ _ _ hm world ha
        cases hs : storeLocal memory (.bytes .vector256 reference) (.scalar (.v256 bits)) <;>
          simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, memory'⟩ := stored
          have hws := storeLocal_preserves_wellFormed _ _ _ _ _ hw hs
          have stored := storeLocal_preserves_static_world _ _ _ _ _ _ updated hs
          cases hr : makeArgumentHomes activation indices args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            cases h
            exact ih memory' final rest other hws stored hr
    · cases h

theorem enterFrame_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (body : CIL.Method) (args : List Value) (m result : Memory) (frame : Frame)
    (hm : m.WellFormed) (world : StaticWorldValid descriptors m)
    (h : enterFrame body args m = .ok (frame, result)) : StaticWorldValid descriptors result := by
  simp only [enterFrame] at h
  cases hl : makeLocals m.nextIdentity body.localKinds body.locals m <;>
    simp only [hl, Bind.bind, Except.bind] at h
  · cases h
  · rename_i locals
    obtain ⟨slots, owned, memory⟩ := locals
    have hw := makeLocals_preserves_wellFormed _ _ _ _ _ _ _ hm hl
    have updated := makeLocals_preserves_static_world _ _ _ _ _ _ _ _ hm world hl
    cases ha : makeArgumentHomes m.nextIdentity body.aggregateArgs args memory <;>
      simp only [ha, Pure.pure, Except.pure] at h
    · cases h
    · rename_i homes
      obtain ⟨arguments, other, final⟩ := homes
      cases h
      exact makeArgumentHomes_preserves_static_world _ _ _ _ _ _ _ _ hw updated ha

#print axioms allocateHome_preserves_static_world
#print axioms storeLocal_preserves_static_world
#print axioms enterFrame_preserves_static_world

end CIL.Safety
