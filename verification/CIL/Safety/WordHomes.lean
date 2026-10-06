import CIL.Safety.WordLocals

namespace CIL.Safety

def wordKinds (specs : List (Option (BitVec 64))) : List CIL.LocalKind :=
  specs.map fun spec => match spec with | none => .reference | some _ => .word64

def wordInitializers (specs : List (Option (BitVec 64))) : List CIL.Value :=
  specs.map fun spec => match spec with | none => .nullRef | some word => .i64 word

/-- Initialized word homes in strictly increasing allocation identities, with
    null root slots retained at their actual metadata positions. -/
inductive WordHomes (memory : Memory) : Nat → List (Option (BitVec 64)) → List LocalSlot → Prop where
  | nil (lower : Nat) : WordHomes memory lower [] []
  | root {lower specs slots} : WordHomes memory lower specs slots →
      WordHomes memory lower (none :: specs) (.root (some .null) :: slots)
  | word {lower specs slots} (reference : Reference) (value : BitVec 64)
      (fresh : lower ≤ reference.allocation)
      (loaded : read memory reference 8 1 = .ok (numberBytes value.toNat 8))
      (writable : access memory reference 8 1 true = .ok ())
      (tail : WordHomes memory (reference.allocation + 1) specs slots) :
      WordHomes memory lower (some value :: specs) (.bytes .word64 reference :: slots)

theorem WordHomes.weaken {memory : Memory} {lower upper : Nat} {specs slots}
    (homes : WordHomes memory upper specs slots) (bound : lower ≤ upper) :
    WordHomes memory lower specs slots := by
  induction homes generalizing lower with
  | nil => exact .nil lower
  | root _ ih => exact .root (ih bound)
  | word reference value fresh loaded writable tail _ =>
    exact .word reference value (Nat.le_trans bound fresh) loaded writable tail

/-- Construct actual typed locals from supported word/root initializers. -/
theorem make_word_locals (memory : Memory) (activation : Nat) (specs : List (Option (BitVec 64)))
    (wellFormed : memory.WellFormed) :
    ∃ slots owned result,
      makeLocals activation (wordKinds specs) (wordInitializers specs) memory = .ok (slots, owned, result) ∧
      WordHomes result memory.nextIdentity specs slots := by
  induction specs generalizing memory with
  | nil => exact ⟨[], [], memory, rfl, .nil _⟩
  | cons spec specs ih =>
    cases spec with
    | none =>
      obtain ⟨slots, owned, result, made, homes⟩ := ih memory wellFormed
      refine ⟨.root (some .null) :: slots, owned, result, ?_, .root homes⟩
      simp only [wordKinds, wordInitializers] at made
      simp only [wordKinds, wordInitializers, List.map_cons, makeLocals, makeLocal, made,
        Bind.bind, Except.bind, Pure.pure, Except.pure, List.nil_append]
    | some value =>
      obtain ⟨reference, middle, made, loaded, writable, _⟩ := make_local_word64 memory activation value wellFormed
      have middleWF := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed made
      obtain ⟨slots, owned, result, rest, homes⟩ := ih middle middleWF
      have fresh := (makeLocal_fresh _ _ _ _ _ _ _ made).2 reference.allocation (by simp)
      have retained := makeLocals_preserves_caller_memory _ _ _ _ _ _ _ rest
      refine ⟨.bytes .word64 reference :: slots, reference.allocation :: owned, result, ?_, ?_⟩
      · simp only [wordKinds, wordInitializers, List.map_cons, makeLocals] at rest ⊢
        rw [made]
        simp only [Bind.bind, Except.bind, rest, Pure.pure, Except.pure, List.singleton_append]
      · exact .word reference value fresh.1
          (by rw [retained.read reference fresh.2 8 1]; exact loaded)
          (by rw [retained.access reference fresh.2 8 1 true]; exact writable)
          (homes.weaken (Nat.succ_le_of_lt fresh.2))


theorem WordHomes.word_at {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (index : Nat) (value : BitVec 64)
    (specified : specs[index]? = some (some value)) :
    ∃ reference, slots[index]? = some (.bytes .word64 reference) ∧ lower ≤ reference.allocation ∧
      read memory reference 8 1 = .ok (numberBytes value.toNat 8) ∧
      access memory reference 8 1 true = .ok () := by
  induction homes generalizing index value with
  | nil => simp at specified
  | root tail ih =>
    cases index with
    | zero => simp at specified
    | succ index => simpa using ih index value (by simpa using specified)
  | word reference initial fresh loaded writable tail ih =>
    cases index with
    | zero =>
      have same : initial = value := by simpa using specified
      subst value
      exact ⟨reference, rfl, fresh, loaded, writable⟩
    | succ index =>
      obtain ⟨r, found, bound, reading, writing⟩ := ih index value (by simpa using specified)
      exact ⟨r, by simpa using found, Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) bound), reading, writing⟩

theorem WordHomes.word_bound {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (index : Nat) (reference : Reference)
    (found : slots[index]? = some (.bytes .word64 reference)) : lower ≤ reference.allocation := by
  induction homes generalizing index with
  | nil => simp at found
  | root tail ih =>
    cases index with
    | zero => simp at found
    | succ index => exact ih index (by simpa using found)
  | word r value fresh loaded writable tail ih =>
    cases index with
    | zero =>
      have same : r = reference := by simpa using found
      simpa only [same] using fresh
    | succ index => exact Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) (ih index (by simpa using found)))

theorem WordHomes.ordered {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (i j : Nat) (left right : Reference)
    (order : i < j) (first : slots[i]? = some (.bytes .word64 left))
    (second : slots[j]? = some (.bytes .word64 right)) : left.allocation < right.allocation := by
  induction homes generalizing i j with
  | nil => simp at first
  | root tail ih =>
    cases i with
    | zero => simp at first
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih i j (by omega) (by simpa using first) (by simpa using second)
  | word r value fresh loaded writable tail ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        have same : r = left := by simpa using first
        have bound := tail.word_bound j right (by simpa using second)
        rw [same] at bound
        exact bound
      | succ i => exact ih i j (by omega) (by simpa using first) (by simpa using second)

#print axioms WordHomes.weaken
#print axioms make_word_locals
#print axioms WordHomes.word_at
#print axioms WordHomes.word_bound
#print axioms WordHomes.ordered

end CIL.Safety
