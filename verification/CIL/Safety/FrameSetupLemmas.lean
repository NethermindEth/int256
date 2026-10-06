import CIL.Safety.FrameLemmas
namespace CIL.Safety

theorem makeLocal_preserves_wellFormed (m result : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (hm : m.WellFormed) (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    result.WellFormed := by
  unfold makeLocal at h
  split at h
  · split at h
    · cases h; exact hm
    · cases h; exact hm
    · cases h
  all_goals
    cases ha : allocateHome m activation (localWidth kind) <;>
      simp only [ha, Bind.bind, Except.bind] at h
    · cases h
    · rename_i home
      obtain ⟨reference, memory⟩ := home
      have hw := allocateHome_preserves_wellFormed _ _ _ _ _ hm ha
      split at h
      · simp only [Pure.pure, Except.pure] at h
        cases h
        exact hw
      · cases hs : storeLocal memory (.bytes kind reference) (.scalar initial) <;>
          simp only [hs, Pure.pure, Except.pure] at h
        · cases h
        · rename_i stored
          obtain ⟨slot', memory'⟩ := stored
          cases h
          exact storeLocal_preserves_wellFormed _ _ _ _ _ hw hs

theorem makeLocals_preserves_wellFormed (m result : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value)
    (slots : List LocalSlot) (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    result.WellFormed := by
  induction kinds generalizing initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; exact hm
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
        cases hr : makeLocals activation kinds initials memory <;>
          simp only [hr, Pure.pure, Except.pure] at h
        · cases h
        · rename_i rest
          obtain ⟨rest, other, final⟩ := rest
          cases h
          exact ih memory final initials rest other hw hr

#print axioms makeLocal_preserves_wellFormed
#print axioms makeLocals_preserves_wellFormed

theorem makeArgumentHomes_preserves_wellFormed (m result : Memory) (activation : Nat)
    (indices : List Nat) (args : List Value) (homes : List (Nat × LocalSlot))
    (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    result.WellFormed := by
  induction indices generalizing m homes owned result with
  | nil => cases h; exact hm
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
        cases hs : storeLocal memory (.bytes .vector256 reference) (.scalar (.v256 bits)) <;>
          simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, memory'⟩ := stored
          have hws := storeLocal_preserves_wellFormed _ _ _ _ _ hw hs
          cases hr : makeArgumentHomes activation indices args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            cases h
            exact ih memory' final rest other hws hr
    · cases h

theorem enterFrame_preserves_wellFormed (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (hm : m.WellFormed)
    (h : enterFrame body args m = .ok (frame, result)) : result.WellFormed := by
  simp only [enterFrame] at h
  cases hl : makeLocals m.nextIdentity body.localKinds body.locals m <;>
    simp only [hl, Bind.bind, Except.bind] at h
  · cases h
  · rename_i locals
    obtain ⟨slots, owned, memory⟩ := locals
    have hw := makeLocals_preserves_wellFormed _ _ _ _ _ _ _ hm hl
    cases ha : makeArgumentHomes m.nextIdentity body.aggregateArgs args memory <;>
      simp only [ha, Pure.pure, Except.pure] at h
    · cases h
    · rename_i homes
      obtain ⟨arguments, other, final⟩ := homes
      cases h
      exact makeArgumentHomes_preserves_wellFormed _ _ _ _ _ _ _ hw ha

#print axioms makeArgumentHomes_preserves_wellFormed
#print axioms enterFrame_preserves_wellFormed
end CIL.Safety
