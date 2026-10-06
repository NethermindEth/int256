import CIL.Safety.FrameSetupLemmas
import CIL.Safety.AllocationExtension
namespace CIL.Safety

theorem allocateHome_fresh (m result : Memory) (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width = .ok (r, result)) :
    AllocationExtension m result ∧ r.allocation = m.nextIdentity ∧
      r.allocation < result.nextIdentity := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, 1, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    have ext := allocate_extends_allocations _ _ _ _ ha
    have ids := allocation_identity_fresh _ _ _ _ ha
    exact ⟨⟨ext.next, ext.lookup⟩, ids.1, by rw [ids.1, ids.2]; exact Nat.lt_succ_self _⟩

theorem storeLocal_extends_allocations (m result : Memory) (slot final : LocalSlot)
    (value : Value) (h : storeLocal m slot value = .ok (final, result)) :
    AllocationExtension m result := by
  cases slot with
  | root root =>
    cases value with
    | scalar value => cases h
    | span reference length => cases h
    | reference reference =>
      simp only [storeLocal] at h
      cases hf : formValue m reference <;>
        simp only [hf, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      · cases h
      · cases h
        exact .refl m
  | bytes kind reference =>
    cases value with
    | reference value => cases h
    | span value length => cases h
    | scalar value =>
      simp only [storeLocal] at h
      cases hn : localNumber kind value <;> simp only [hn, Bind.bind, Except.bind] at h
      · cases h
      · rename_i number
        cases hw : write m reference (numberBytes number (localWidth kind)) 1 <;>
          simp only [hw, checkedAt, Except.mapError, Pure.pure, Except.pure] at h
        · cases h
        · cases h
          exact write_extends_allocations _ _ _ _ _ hw

def FreshOwned (before after : Memory) (owned : List AllocationId) : Prop :=
  AllocationExtension before after ∧
    ∀ id ∈ owned, before.nextIdentity ≤ id ∧ id < after.nextIdentity

theorem makeLocal_fresh (m result : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    FreshOwned m result owned := by
  unfold makeLocal at h
  split at h
  · split at h
    · cases h; exact ⟨.refl m, by simp⟩
    · cases h; exact ⟨.refl m, by simp⟩
    · cases h
  all_goals
    cases ha : allocateHome m activation (localWidth kind) <;>
      simp only [ha, Bind.bind, Except.bind] at h
    · cases h
    · rename_i home
      obtain ⟨reference, memory⟩ := home
      have fresh := allocateHome_fresh _ _ _ _ _ ha
      split at h
      · simp only [Pure.pure, Except.pure] at h
        cases h
        refine ⟨fresh.1, ?_⟩
        intro id member
        simp only [List.mem_singleton] at member
        subst id
        exact ⟨by rw [fresh.2.1]; exact Nat.le_refl _, fresh.2.2⟩
      · cases hs : storeLocal memory (.bytes kind reference) (.scalar initial) <;>
          simp only [hs, Pure.pure, Except.pure] at h
        · cases h
        · rename_i stored
          obtain ⟨slot', memory'⟩ := stored
          cases h
          have ext := storeLocal_extends_allocations _ _ _ _ _ hs
          refine ⟨fresh.1.trans ext, ?_⟩
          intro id member
          simp only [List.mem_singleton] at member
          subst id
          exact ⟨by rw [fresh.2.1]; exact Nat.le_refl _, Nat.lt_of_lt_of_le fresh.2.2 ext.next⟩

#print axioms makeLocal_fresh

theorem FreshOwned.trans {first middle last : Memory} {left right : List AllocationId}
    (hl : FreshOwned first middle left) (hr : FreshOwned middle last right) :
    FreshOwned first last (left ++ right) := by
  refine ⟨hl.1.trans hr.1, ?_⟩
  intro id member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨lo, hi⟩ := hl.2 id member
    exact ⟨lo, Nat.lt_of_lt_of_le hi hr.1.next⟩
  · obtain ⟨lo, hi⟩ := hr.2 id member
    exact ⟨Nat.le_trans hl.1.next lo, hi⟩

theorem makeLocals_fresh (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    FreshOwned m result owned := by
  induction kinds generalizing initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; exact ⟨.refl m, by simp⟩
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
        have fresh := makeLocal_fresh _ _ _ _ _ _ _ hl
        cases hr : makeLocals activation kinds initials memory <;>
          simp only [hr, Pure.pure, Except.pure] at h
        · cases h
        · rename_i rest
          obtain ⟨rest, other, final⟩ := rest
          cases h
          exact fresh.trans (ih memory final initials rest other hr)

theorem makeArgumentHomes_fresh (m result : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    FreshOwned m result owned := by
  induction indices generalizing m homes owned result with
  | nil => cases h; exact ⟨.refl m, by simp⟩
  | cons index indices ih =>
    simp only [makeArgumentHomes] at h
    split at h
    · rename_i bits hv
      cases ha : allocateHome m activation (localWidth .vector256) <;>
        simp only [ha, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨reference, memory⟩ := home
        have fresh := allocateHome_fresh _ _ _ _ _ ha
        cases hs : storeLocal memory (.bytes .vector256 reference) (.scalar (.v256 bits)) <;>
          simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, memory'⟩ := stored
          have ext := storeLocal_extends_allocations _ _ _ _ _ hs
          have first : FreshOwned m memory' [reference.allocation] := by
            refine ⟨fresh.1.trans ext, ?_⟩
            intro id member
            simp only [List.mem_singleton] at member
            subst id
            exact ⟨by rw [fresh.2.1]; exact Nat.le_refl _, Nat.lt_of_lt_of_le fresh.2.2 ext.next⟩
          cases hr : makeArgumentHomes activation indices args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            cases h
            exact first.trans (ih memory' final rest other hr)
    · cases h

theorem enterFrame_fresh (body : CIL.Method) (args : List Value) (m result : Memory) (frame : Frame)
    (h : enterFrame body args m = .ok (frame, result)) : FreshOwned m result frame.owned := by
  simp only [enterFrame] at h
  cases hl : makeLocals m.nextIdentity body.localKinds body.locals m <;>
    simp only [hl, Bind.bind, Except.bind] at h
  · cases h
  · rename_i locals
    obtain ⟨slots, owned, memory⟩ := locals
    have fresh := makeLocals_fresh _ _ _ _ _ _ _ hl
    cases ha : makeArgumentHomes m.nextIdentity body.aggregateArgs args memory <;>
      simp only [ha, Pure.pure, Except.pure] at h
    · cases h
    · rename_i homes
      obtain ⟨arguments, other, final⟩ := homes
      cases h
      exact fresh.trans (makeArgumentHomes_fresh _ _ _ _ _ _ _ ha)

theorem leaveFrame_preserves_older_allocations (frame : Frame) (m : Memory) (watermark : Nat)
    (fresh : ∀ id ∈ frame.owned, watermark ≤ id) (id : AllocationId) (old : id < watermark) :
    (leaveFrame frame m).allocations id = m.allocations id := by
  have notOwned : id ∉ frame.owned := by
    intro owned
    exact Nat.not_lt_of_ge (fresh id owned) old
  simp [leaveFrame, expireAll_allocations, notOwned]

theorem frame_entry_exit_preserves_caller (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (id : AllocationId)
    (h : enterFrame body args m = .ok (frame, result)) (old : id < m.nextIdentity) :
    (leaveFrame frame result).allocations id = m.allocations id := by
  have fresh := enterFrame_fresh _ _ _ _ _ h
  rw [leaveFrame_preserves_older_allocations frame result m.nextIdentity
    (fun id member => (fresh.2 id member).1) id old]
  exact fresh.1.lookup id old

#print axioms enterFrame_fresh
#print axioms leaveFrame_preserves_older_allocations
#print axioms frame_entry_exit_preserves_caller

theorem frame_entry_exit_preserves_reference (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (r formed : Reference) (hm : m.WellFormed)
    (enter : enterFrame body args m = .ok (frame, result)) (valid : form m r = .ok formed) :
    form (leaveFrame frame result) r = .ok formed := by
  obtain ⟨a, present, _, _⟩ := formed_reference_live _ _ _ valid
  have old := (hm.1 _ _ present).1
  rw [form_allocation_congr _ _ _ (frame_entry_exit_preserves_caller _ _ _ _ _ _ enter old)]
  exact valid

#print axioms frame_entry_exit_preserves_reference

theorem expireAll_retained_fields (ids : List AllocationId) (m : Memory) :
    (ids.foldl expire m).cells = m.cells ∧ (ids.foldl expire m).views = m.views ∧
    (ids.foldl expire m).staticBindings = m.staticBindings ∧
    (ids.foldl expire m).nextIdentity = m.nextIdentity := by
  induction ids generalizing m with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons id ids ih => exact ih (expire m id)
end CIL.Safety
