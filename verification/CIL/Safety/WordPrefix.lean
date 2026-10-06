import CIL.Safety.WordHomes
import CIL.Safety.FrameProgress

namespace CIL.Safety

/-- Retain initialized word/root homes before an arbitrary validated typed
    suffix. Suffix allocations/writes cannot alter the earlier word homes. -/
theorem make_word_prefix (memory : Memory) (activation : Nat) (specs : List (Option (BitVec 64)))
    (tailKinds : List CIL.LocalKind) (tailValues : List CIL.Value)
    (wellFormed : memory.WellFormed) (fits : InitializersFit tailKinds tailValues) :
    ∃ slots tailSlots owned result,
      makeLocals activation (wordKinds specs ++ tailKinds) (wordInitializers specs ++ tailValues) memory =
        .ok (slots ++ tailSlots, owned, result) ∧ WordHomes result memory.nextIdentity specs slots := by
  induction specs generalizing memory with
  | nil =>
    obtain ⟨slots, owned, result, made⟩ := makeLocals_succeeds memory activation tailKinds tailValues wellFormed fits
    exact ⟨[], slots, owned, result, made, .nil _⟩
  | cons spec specs ih =>
    cases spec with
    | none =>
      obtain ⟨slots, tailSlots, owned, result, made, homes⟩ := ih memory wellFormed
      refine ⟨.root (some .null) :: slots, tailSlots, owned, result, ?_, .root homes⟩
      simp only [wordKinds, wordInitializers] at made
      simp only [wordKinds, wordInitializers, List.map_cons, List.cons_append, makeLocals, makeLocal, made,
        Bind.bind, Except.bind, Pure.pure, Except.pure, List.nil_append]
    | some value =>
      obtain ⟨reference, middle, made, loaded, writable, _⟩ := make_local_word64 memory activation value wellFormed
      have middleWF := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed made
      obtain ⟨slots, tailSlots, owned, result, rest, homes⟩ := ih middle middleWF
      have fresh := (makeLocal_fresh _ _ _ _ _ _ _ made).2 reference.allocation (by simp)
      have retained := makeLocals_preserves_caller_memory _ _ _ _ _ _ _ rest
      refine ⟨.bytes .word64 reference :: slots, tailSlots, reference.allocation :: owned, result, ?_, ?_⟩
      · simp only [wordKinds, wordInitializers, List.map_cons, List.cons_append, makeLocals] at rest ⊢
        rw [made]
        simp only [Bind.bind, Except.bind, rest, Pure.pure, Except.pure, List.singleton_append]
      · exact .word reference value fresh.1
          (by rw [retained.read reference fresh.2 8 1]; exact loaded)
          (by rw [retained.access reference fresh.2 8 1 true]; exact writable)
          (homes.weaken (Nat.succ_le_of_lt fresh.2))

theorem WordHomes.length {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) : slots.length = specs.length := by
  induction homes <;> simp_all

#print axioms make_word_prefix
#print axioms WordHomes.length

end CIL.Safety
