import CIL.Safety.NumericLocals

namespace CIL.Safety

/-- A numeric local initializer whose extracted storage kind accepts the value. -/
structure NumericLocalSpec where
  kind : CIL.LocalKind
  value : CIL.Value
  number : Nat
  fits : localNumber kind value = .ok number

def numericKinds (specs : List NumericLocalSpec) : List CIL.LocalKind := specs.map (·.kind)
def numericInitializers (specs : List NumericLocalSpec) : List CIL.Value := specs.map (·.value)

/-- Initialized writable homes in strictly increasing allocation identities. -/
inductive NumericHomes (memory : Memory) : Nat → List NumericLocalSpec → List LocalSlot → Prop where
  | nil (lower : Nat) : NumericHomes memory lower [] []
  | cons {lower specs slots} (reference : Reference) (spec : NumericLocalSpec)
      (fresh : lower ≤ reference.allocation)
      (loaded : read memory reference (localWidth spec.kind) 1 =
        .ok (numberBytes spec.number (localWidth spec.kind)))
      (writable : access memory reference (localWidth spec.kind) 1 true = .ok ())
      (tail : NumericHomes memory (reference.allocation + 1) specs slots) :
      NumericHomes memory lower (spec :: specs) (.bytes spec.kind reference :: slots)

theorem NumericHomes.weaken {memory : Memory} {lower upper : Nat} {specs slots}
    (homes : NumericHomes memory upper specs slots) (bound : lower ≤ upper) :
    NumericHomes memory lower specs slots := by
  cases homes with
  | nil => exact .nil lower
  | cons reference spec fresh loaded writable tail =>
    exact .cons reference spec (Nat.le_trans bound fresh) loaded writable tail

theorem make_numeric_locals (memory : Memory) (activation : Nat) (specs : List NumericLocalSpec)
    (wellFormed : memory.WellFormed) :
    ∃ slots owned result,
      makeLocals activation (numericKinds specs) (numericInitializers specs) memory =
        .ok (slots, owned, result) ∧ NumericHomes result memory.nextIdentity specs slots := by
  induction specs generalizing memory with
  | nil => exact ⟨[], [], memory, rfl, .nil _⟩
  | cons spec specs ih =>
    obtain ⟨reference, middle, made, loaded, writable, _⟩ :=
      make_numeric_local memory activation spec.kind spec.value spec.number wellFormed spec.fits
    have middleWF := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed made
    obtain ⟨slots, owned, result, rest, homes⟩ := ih middle middleWF
    have fresh := (makeLocal_fresh _ _ _ _ _ _ _ made).2 reference.allocation (by simp)
    have retained := makeLocals_preserves_caller_memory _ _ _ _ _ _ _ rest
    refine ⟨.bytes spec.kind reference :: slots, reference.allocation :: owned, result, ?_, ?_⟩
    · simp only [numericKinds, numericInitializers] at rest
      simp only [numericKinds, numericInitializers, List.map_cons, makeLocals]
      rw [made]
      simp only [Bind.bind, Except.bind, rest, Pure.pure, Except.pure, List.singleton_append]
    · exact .cons reference spec fresh.1
        (by rw [retained.read reference fresh.2 (localWidth spec.kind) 1]; exact loaded)
        (by rw [retained.access reference fresh.2 (localWidth spec.kind) 1 true]; exact writable)
        (homes.weaken (Nat.succ_le_of_lt fresh.2))

theorem NumericHomes.home_at {memory : Memory} {lower : Nat} {specs slots}
    (homes : NumericHomes memory lower specs slots) (index : Nat) (spec : NumericLocalSpec)
    (specified : specs[index]? = some spec) :
    ∃ reference, slots[index]? = some (.bytes spec.kind reference) ∧ lower ≤ reference.allocation ∧
      read memory reference (localWidth spec.kind) 1 = .ok (numberBytes spec.number (localWidth spec.kind)) ∧
      access memory reference (localWidth spec.kind) 1 true = .ok () := by
  induction homes generalizing index spec with
  | nil => simp at specified
  | cons reference initial fresh loaded writable tail ih =>
    cases index with
    | zero =>
      have same : initial = spec := by simpa using specified
      subst spec
      exact ⟨reference, rfl, fresh, loaded, writable⟩
    | succ index =>
      obtain ⟨r, slot, bound, readback, accessOK⟩ := ih index spec (by simpa using specified)
      exact ⟨r, by simpa using slot, Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) bound), readback, accessOK⟩

/-- Every numeric home is above the caller's allocation boundary. -/
theorem NumericHomes.home_bound {memory : Memory} {lower : Nat} {specs slots}
    (homes : NumericHomes memory lower specs slots) (index : Nat) (kind : CIL.LocalKind)
    (reference : Reference) (found : slots[index]? = some (.bytes kind reference)) :
    lower ≤ reference.allocation := by
  induction homes generalizing index with
  | nil => simp at found
  | cons r spec fresh loaded writable tail ih =>
    cases index with
    | zero =>
      have same : r = reference := (by simpa using found : spec.kind = kind ∧ r = reference).2
      simpa only [same] using fresh
    | succ index =>
      exact Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) (ih index (by simpa using found)))

/-- Distinct numeric slots have distinct allocation identities, including
    mixed word/vector frames. No separation of caller operands is required. -/
theorem NumericHomes.ordered {memory : Memory} {lower : Nat} {specs slots}
    (homes : NumericHomes memory lower specs slots) (i j : Nat)
    (leftKind rightKind : CIL.LocalKind) (left right : Reference)
    (order : i < j) (first : slots[i]? = some (.bytes leftKind left))
    (second : slots[j]? = some (.bytes rightKind right)) :
    left.allocation < right.allocation := by
  induction homes generalizing i j with
  | nil => simp at first
  | cons r spec fresh loaded writable tail ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        have same : r = left := (by simpa using first : spec.kind = leftKind ∧ r = left).2
        have bound := tail.home_bound j rightKind right (by simpa using second)
        rw [same] at bound
        exact bound
      | succ i => exact ih i j (by omega) (by simpa using first) (by simpa using second)

#print axioms NumericHomes.home_bound
#print axioms NumericHomes.ordered
#print axioms NumericHomes.weaken
#print axioms make_numeric_locals
#print axioms NumericHomes.home_at
/-- Propose numeric recipes from metadata. Callers must prove both metadata
    lists equal the resulting recipe, so rejected pairs or truncation cannot pass. -/
def numericSpecs (body : CIL.Method) : List NumericLocalSpec :=
  (body.localKinds.zip body.locals).filterMap fun (kind, value) =>
    match h : localNumber kind value with
    | .ok number => some ⟨kind, value, number, h⟩
    | .error _ => none

/-- Actual extracted local metadata must match the validated recipe exactly. -/
theorem numeric_frame_setup (body : CIL.Method) (specs : List NumericLocalSpec)
    (kinds : body.localKinds = specs.map NumericLocalSpec.kind)
    (initializers : body.locals = specs.map NumericLocalSpec.value)
    (arguments : body.aggregateArgs = []) (memory : Memory) (args : List Value)
    (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame body args memory = .ok (frame, result) ∧
      NumericHomes result memory.nextIdentity specs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨slots, owned, result, made, homes⟩ := make_numeric_locals memory memory.nextIdentity specs wellFormed
  simp only [numericKinds, numericInitializers] at made
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have setup : enterFrame body args memory = .ok (frame, result) := by
    simp only [enterFrame, kinds, initializers, made, arguments, makeArgumentHomes,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
    rfl
  exact ⟨frame, result, setup, homes, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
    enterFrame_preserves_wellFormed _ _ _ _ _ wellFormed setup⟩

#print axioms numeric_frame_setup
end CIL.Safety
