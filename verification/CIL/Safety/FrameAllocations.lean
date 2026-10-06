import CIL.Safety.FrameOwnership
namespace CIL.Safety

def FrameAllocations (m : Memory) (activation : Nat) (owned : List AllocationId) : Prop :=
  ∀ id ∈ owned, ∃ a, m.allocations id = some a ∧ a.kind = .frame activation ∧ a.live = true

theorem FrameAllocations.preserve {before after : Memory} {activation : Nat} {owned : List AllocationId}
    (ext : AllocationExtension before after) (bounds : ∀ id ∈ owned, id < before.nextIdentity)
    (owns : FrameAllocations before activation owned) : FrameAllocations after activation owned := by
  intro id member
  obtain ⟨a, present, kind, live⟩ := owns id member
  exact ⟨a, (ext.lookup id (bounds id member)).trans present, kind, live⟩

theorem FrameAllocations.append {m : Memory} {activation : Nat} {left right : List AllocationId}
    (hl : FrameAllocations m activation left) (hr : FrameAllocations m activation right) :
    FrameAllocations m activation (left ++ right) := by
  intro id member
  rcases List.mem_append.mp member with member | member
  · exact hl id member
  · exact hr id member

theorem allocateHome_owned (m result : Memory) (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width = .ok (r, result)) :
    FrameAllocations result activation [r.allocation] := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, 1, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    intro other member
    simp only [List.mem_singleton] at member
    subst other
    have lookup := allocation_lookup m _ id memory ha
    exact ⟨_, lookup, rfl, rfl⟩

theorem makeLocal_owned (m result : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    FrameAllocations result activation owned := by
  unfold makeLocal at h
  split at h
  · split at h
    · cases h; intro id member; cases member
    · cases h; intro id member; cases member
    · cases h
  all_goals
    cases ha : allocateHome m activation (localWidth kind) <;>
      simp only [ha, Bind.bind, Except.bind] at h
    · cases h
    · rename_i home
      obtain ⟨reference, memory⟩ := home
      have owns := allocateHome_owned _ _ _ _ _ ha
      have fresh := allocateHome_fresh _ _ _ _ _ ha
      split at h
      · simp only [Pure.pure, Except.pure] at h
        cases h
        exact owns
      · cases hs : storeLocal memory (.bytes kind reference) (.scalar initial) <;>
          simp only [hs, Pure.pure, Except.pure] at h
        · cases h
        · rename_i stored
          obtain ⟨slot', memory'⟩ := stored
          cases h
          apply owns.preserve (storeLocal_extends_allocations _ _ _ _ _ hs)
          intro id member
          simp only [List.mem_singleton] at member
          subst id
          exact fresh.2.2

theorem makeLocals_owned (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    FrameAllocations result activation owned := by
  induction kinds generalizing initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; intro id member; cases member
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
        have owns := makeLocal_owned _ _ _ _ _ _ _ hl
        have first := makeLocal_fresh _ _ _ _ _ _ _ hl
        cases hr : makeLocals activation kinds initials memory <;>
          simp only [hr, Pure.pure, Except.pure] at h
        · cases h
        · rename_i rest
          obtain ⟨rest, other, final⟩ := rest
          cases h
          have next := makeLocals_fresh _ _ _ _ _ _ _ hr
          exact (owns.preserve next.1 (fun id member => (first.2 id member).2)).append
            (ih memory final initials rest other hr)

#print axioms makeLocals_owned

theorem makeArgumentHomes_owned (m result : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    FrameAllocations result activation owned := by
  induction indices generalizing m homes owned result with
  | nil => cases h; intro id member; cases member
  | cons index indices ih =>
    simp only [makeArgumentHomes] at h
    split at h
    · rename_i bits hv
      cases ha : allocateHome m activation (localWidth .vector256) <;>
        simp only [ha, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨reference, memory⟩ := home
        have owns := allocateHome_owned _ _ _ _ _ ha
        have fresh := allocateHome_fresh _ _ _ _ _ ha
        cases hs : storeLocal memory (.bytes .vector256 reference) (.scalar (.v256 bits)) <;>
          simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, memory'⟩ := stored
          have ext := storeLocal_extends_allocations _ _ _ _ _ hs
          have first : FrameAllocations memory' activation [reference.allocation] := by
            apply owns.preserve ext
            intro id member
            simp only [List.mem_singleton] at member
            subst id
            exact fresh.2.2
          cases hr : makeArgumentHomes activation indices args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            cases h
            have next := makeArgumentHomes_fresh _ _ _ _ _ _ _ hr
            have older : ∀ id ∈ [reference.allocation], id < memory'.nextIdentity := by
              intro id member
              simp only [List.mem_singleton] at member
              subst id
              exact Nat.lt_of_lt_of_le fresh.2.2 ext.next
            exact (first.preserve next.1 older).append (ih memory' final rest other hr)
    · cases h

theorem enterFrame_owned (body : CIL.Method) (args : List Value) (m result : Memory) (frame : Frame)
    (h : enterFrame body args m = .ok (frame, result)) :
    FrameAllocations result frame.activation frame.owned := by
  simp only [enterFrame] at h
  cases hl : makeLocals m.nextIdentity body.localKinds body.locals m <;>
    simp only [hl, Bind.bind, Except.bind] at h
  · cases h
  · rename_i locals
    obtain ⟨slots, owned, memory⟩ := locals
    have owns := makeLocals_owned _ _ _ _ _ _ _ hl
    have fresh := makeLocals_fresh _ _ _ _ _ _ _ hl
    cases ha : makeArgumentHomes m.nextIdentity body.aggregateArgs args memory <;>
      simp only [ha, Pure.pure, Except.pure] at h
    · cases h
    · rename_i homes
      obtain ⟨arguments, other, final⟩ := homes
      cases h
      have next := makeArgumentHomes_fresh _ _ _ _ _ _ _ ha
      exact (owns.preserve next.1 (fun id member => (fresh.2 id member).2)).append
        (makeArgumentHomes_owned _ _ _ _ _ _ _ ha)

#print axioms enterFrame_owned
end CIL.Safety
