import CIL.Safety.LiveValues
import CIL.Safety.FrameAllocations

namespace CIL.Safety

/-- An uninitialized root is legal storage, but loadLocal still rejects it.
    Numeric-home initialization and access width remain separate obligations. -/
def LocalSlot.ReferencesValid (m : Memory) : LocalSlot → Prop
  | .root none => True
  | .root (some r) => (Value.reference r).Valid m
  | .bytes _ r => form m r = .ok r

def SlotsReferencesValid (m : Memory) (slots : List LocalSlot) : Prop :=
  ∀ slot ∈ slots, slot.ReferencesValid m

theorem LocalSlot.ReferencesValid.preserve {m result : Memory} {slot : LocalSlot}
    (valid : slot.ReferencesValid m) (hm : m.WellFormed) (ext : AllocationExtension m result) :
    slot.ReferencesValid result := by
  cases slot with
  | bytes kind r => exact ext.preserves_reference hm r r valid
  | root value =>
    cases value with
    | none => exact True.intro
    | some r =>
      cases r with
      | null => exact True.intro
      | address r => exact ext.preserves_reference hm r r valid

theorem allocateHome_reference_valid (m result : Memory) (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width = .ok (r, result)) : form result r = .ok r := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, 1, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    have lookup := allocation_lookup m _ id memory ha
    have position : 0 < width ∨ 0 = width := by omega
    simp [form, liveAllocation, lookup, validPosition, nativeLimit, position,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem storeLocal_preserves_reference_validity (m result : Memory) (slot final : LocalSlot)
    (value : Value) (hm : m.WellFormed) (valid : slot.ReferencesValid m)
    (h : storeLocal m slot value = .ok (final, result)) : final.ReferencesValid result := by
  have ext := storeLocal_extends_allocations _ _ _ _ _ h
  have retained := valid.preserve hm ext
  unfold storeLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact retained
      | solve |
          change (Value.reference _).Valid _
          have checked := formValue_result_valid _ _ _ (by assumption)
          have same := formValue_returns_input _ _ _ (by assumption)
          rw [same] at checked
          exact checked
      | cases h
      | split at h

theorem loadLocal_result_valid (m : Memory) (slot : LocalSlot) (value : Value)
    (h : loadLocal m slot = .ok value) : value.Valid m := by
  unfold loadLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | rfl
      | solve | apply formValue_result_valid; assumption
      | cases h
      | split at h

theorem localAddress_result_valid (m : Memory) (slot : LocalSlot) (value : Value)
    (h : localAddress m slot = .ok value) : value.Valid m := by
  cases slot with
  | root root => cases h
  | bytes kind r => exact formValue_result_valid m (.address r) value h

theorem makeLocal_reference_valid (m result : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    slot.ReferencesValid result := by
  unfold makeLocal at h
  split at h
  · split at h
    · cases h; exact True.intro
    · cases h; exact True.intro
    · cases h
  all_goals
    cases ha : allocateHome m activation (localWidth kind) <;>
      simp only [ha, Bind.bind, Except.bind] at h
    · cases h
    · rename_i home
      obtain ⟨r, memory⟩ := home
      have valid := allocateHome_reference_valid _ _ _ _ _ ha
      have hw := allocateHome_preserves_wellFormed _ _ _ _ _ hm ha
      split at h
      · simp only [Pure.pure, Except.pure] at h
        cases h
        exact valid
      · cases hs : storeLocal memory (.bytes kind r) (.scalar initial) <;>
          simp only [hs, Pure.pure, Except.pure] at h
        · cases h
        · rename_i stored
          obtain ⟨slot', memory'⟩ := stored
          cases h
          exact storeLocal_preserves_reference_validity _ _ (.bytes kind r) _ _ hw valid hs

theorem makeLocals_references_valid (m result : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value) (slots : List LocalSlot)
    (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    SlotsReferencesValid result slots := by
  induction kinds generalizing initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; simp [SlotsReferencesValid]
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
        have valid := makeLocal_reference_valid _ _ _ _ _ _ _ hm hl
        have hw := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ hm hl
        cases hr : makeLocals activation kinds initials memory <;>
          simp only [hr, Pure.pure, Except.pure] at h
        · cases h
        · rename_i rest
          obtain ⟨rest, other, final⟩ := rest
          have tail := ih memory final initials rest other hw hr
          have retained := valid.preserve hw (makeLocals_fresh _ _ _ _ _ _ _ hr).1
          cases h
          intro slot member
          rcases List.mem_cons.mp member with rfl | member
          · exact retained
          · exact tail _ member

theorem makeArgumentHomes_references_valid (m result : Memory) (activation : Nat)
    (indices : List Nat) (args : List Value) (homes : List (Nat × LocalSlot))
    (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    ∀ home ∈ homes, home.2.ReferencesValid result := by
  induction indices generalizing m homes owned result with
  | nil => cases h; simp
  | cons index indices ih =>
    simp only [makeArgumentHomes] at h
    split at h
    · rename_i bits hv
      cases ha : allocateHome m activation (localWidth .vector256) <;>
        simp only [ha, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨r, memory⟩ := home
        have valid := allocateHome_reference_valid _ _ _ _ _ ha
        have hw := allocateHome_preserves_wellFormed _ _ _ _ _ hm ha
        cases hs : storeLocal memory (.bytes .vector256 r) (.scalar (.v256 bits)) <;>
          simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, memory'⟩ := stored
          have storedValid := storeLocal_preserves_reference_validity _ _ (.bytes .vector256 r) _ _ hw valid hs
          have storedWF := storeLocal_preserves_wellFormed _ _ _ _ _ hw hs
          cases hr : makeArgumentHomes activation indices args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            have tail := ih memory' final rest other storedWF hr
            have retained := storedValid.preserve storedWF (makeArgumentHomes_fresh _ _ _ _ _ _ _ hr).1
            cases h
            intro home member
            rcases List.mem_cons.mp member with rfl | member
            · exact retained
            · exact tail _ member
    · cases h

def Frame.ReferencesValid (m : Memory) (frame : Frame) : Prop :=
  SlotsReferencesValid m frame.locals ∧ ∀ home ∈ frame.arguments, home.2.ReferencesValid m

theorem enterFrame_references_valid (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (hm : m.WellFormed)
    (h : enterFrame body args m = .ok (frame, result)) : frame.ReferencesValid result := by
  simp only [enterFrame] at h
  cases hl : makeLocals m.nextIdentity body.localKinds body.locals m <;>
    simp only [hl, Bind.bind, Except.bind] at h
  · cases h
  · rename_i locals
    obtain ⟨slots, owned, memory⟩ := locals
    have localsValid := makeLocals_references_valid _ _ _ _ _ _ _ hm hl
    have hw := makeLocals_preserves_wellFormed _ _ _ _ _ _ _ hm hl
    cases ha : makeArgumentHomes m.nextIdentity body.aggregateArgs args memory <;>
      simp only [ha, Pure.pure, Except.pure] at h
    · cases h
    · rename_i homes
      obtain ⟨arguments, other, final⟩ := homes
      have argumentsValid := makeArgumentHomes_references_valid _ _ _ _ _ _ _ hw ha
      have ext := (makeArgumentHomes_fresh _ _ _ _ _ _ _ ha).1
      cases h
      exact ⟨fun slot member => (localsValid slot member).preserve hw ext, argumentsValid⟩

theorem Frame.ReferencesValid.preserve {m result : Memory} {frame : Frame}
    (valid : frame.ReferencesValid m) (hm : m.WellFormed) (ext : AllocationExtension m result) :
    frame.ReferencesValid result :=
  ⟨fun slot member => (valid.1 slot member).preserve hm ext,
    fun home member => (valid.2 home member).preserve hm ext⟩

#print axioms allocateHome_reference_valid
#print axioms storeLocal_preserves_reference_validity
#print axioms loadLocal_result_valid
#print axioms makeLocals_references_valid
#print axioms enterFrame_references_valid
#print axioms Frame.ReferencesValid.preserve

end CIL.Safety
