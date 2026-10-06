import CIL.Safety.FrameProgress
import CIL.Safety.FrameMemoryBelow

namespace CIL.Safety

/-- Typed writable storage, with no assertion that its bytes are initialized. -/
inductive WritableHomes (memory : Memory) : Nat → List CIL.LocalKind → List LocalSlot → Prop where
  | nil (lower : Nat) : WritableHomes memory lower [] []
  | cons {lower kinds slots} (reference : Reference) (kind : CIL.LocalKind)
      (fresh : lower ≤ reference.allocation)
      (writable : access memory reference (localWidth kind) 1 true = .ok ())
      (tail : WritableHomes memory (reference.allocation + 1) kinds slots) :
      WritableHomes memory lower (kind :: kinds) (.bytes kind reference :: slots)

theorem WritableHomes.weaken {memory : Memory} {lower upper : Nat} {kinds slots}
    (homes : WritableHomes memory upper kinds slots) (bound : lower ≤ upper) :
    WritableHomes memory lower kinds slots := by
  cases homes with
  | nil => exact .nil lower
  | cons reference kind fresh writable tail =>
    exact .cons reference kind (Nat.le_trans bound fresh) writable tail

theorem make_unknown_local (memory : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (wellFormed : memory.WellFormed) (numeric : kind ≠ .reference) :
    ∃ reference result,
      makeLocal activation kind .unmodeled memory =
        .ok (.bytes kind reference, [reference.allocation], result) ∧
      access result reference (localWidth kind) 1 true = .ok () := by
  obtain ⟨reference, result, home⟩ :=
    allocateHome_succeeds memory activation (localWidth kind) wellFormed (localWidth_bounded kind)
  refine ⟨reference, result, ?_, (allocateHome_write_access _ _ _ _ _ home).access⟩
  cases kind <;> simp_all [makeLocal, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem make_unknown_locals (memory : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (wellFormed : memory.WellFormed) (numeric : ∀ kind ∈ kinds, kind ≠ .reference) :
    ∃ slots owned result,
      makeLocals activation kinds (kinds.map fun _ => .unmodeled) memory =
        .ok (slots, owned, result) ∧ WritableHomes result memory.nextIdentity kinds slots := by
  induction kinds generalizing memory with
  | nil => exact ⟨[], [], memory, rfl, .nil _⟩
  | cons kind kinds ih =>
    obtain ⟨reference, middle, made, writable⟩ :=
      make_unknown_local memory activation kind wellFormed (numeric kind (by simp))
    have middleWF := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed made
    obtain ⟨slots, owned, result, rest, homes⟩ :=
      ih middle middleWF (fun k member => numeric k (by simp [member]))
    have fresh := (makeLocal_fresh _ _ _ _ _ _ _ made).2 reference.allocation (by simp)
    have retained := makeLocals_preserves_caller_memory _ _ _ _ _ _ _ rest
    refine ⟨.bytes kind reference :: slots, reference.allocation :: owned, result, ?_, ?_⟩
    · simp only [List.map_cons, makeLocals, made, Bind.bind, Except.bind, rest,
        Pure.pure, Except.pure, List.singleton_append]
    · exact .cons reference kind fresh.1
        ((retained.access reference fresh.2 (localWidth kind) 1 true).trans writable)
        (homes.weaken (Nat.succ_le_of_lt fresh.2))

theorem WritableHomes.home_at {memory : Memory} {lower : Nat} {kinds slots}
    (homes : WritableHomes memory lower kinds slots) (index : Nat) (kind : CIL.LocalKind)
    (specified : kinds[index]? = some kind) :
    ∃ reference, slots[index]? = some (.bytes kind reference) ∧ lower ≤ reference.allocation ∧
      access memory reference (localWidth kind) 1 true = .ok () := by
  induction homes generalizing index kind with
  | nil => simp at specified
  | cons reference initial fresh writable tail ih =>
    cases index with
    | zero =>
      have same : initial = kind := by simpa using specified
      subst kind
      exact ⟨reference, rfl, fresh, writable⟩
    | succ index =>
      obtain ⟨r, slot, bound, accessOK⟩ := ih index kind (by simpa using specified)
      exact ⟨r, by simpa using slot, Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) bound), accessOK⟩

theorem unknown_frame_setup (body : CIL.Method)
    (initializers : body.locals = body.localKinds.map fun _ => .unmodeled)
    (numeric : ∀ kind ∈ body.localKinds, kind ≠ .reference)
    (arguments : body.aggregateArgs = []) (memory : Memory) (args : List Value)
    (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame body args memory = .ok (frame, result) ∧
      WritableHomes result memory.nextIdentity body.localKinds frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨slots, owned, result, made, homes⟩ :=
    make_unknown_locals memory memory.nextIdentity body.localKinds wellFormed numeric
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have setup : enterFrame body args memory = .ok (frame, result) := by
    simp only [enterFrame, initializers, made, arguments, makeArgumentHomes,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
    rfl
  exact ⟨frame, result, setup, homes, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
    enterFrame_preserves_wellFormed _ _ _ _ _ wellFormed setup⟩

theorem WritableHomes.home_bound {memory : Memory} {lower : Nat} {kinds slots}
    (homes : WritableHomes memory lower kinds slots) (index : Nat) (kind : CIL.LocalKind)
    (reference : Reference) (found : slots[index]? = some (.bytes kind reference)) :
    lower ≤ reference.allocation := by
  induction homes generalizing index with
  | nil => simp at found
  | cons r initial fresh writable tail ih =>
    cases index with
    | zero =>
      have same : r = reference := (by simpa using found : initial = kind ∧ r = reference).2
      simpa only [same] using fresh
    | succ index => exact Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) (ih index (by simpa using found)))

/-- Separate private homes cannot overwrite each other's initialized bytes. -/
theorem WritableHomes.ordered {memory : Memory} {lower : Nat} {kinds slots}
    (homes : WritableHomes memory lower kinds slots) (i j : Nat)
    (leftKind rightKind : CIL.LocalKind) (left right : Reference)
    (order : i < j) (first : slots[i]? = some (.bytes leftKind left))
    (second : slots[j]? = some (.bytes rightKind right)) :
    left.allocation < right.allocation := by
  induction homes generalizing i j with
  | nil => simp at first
  | cons r kind fresh writable tail ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        have same : r = left := (by simpa using first : kind = leftKind ∧ r = left).2
        have bound := tail.home_bound j rightKind right (by simpa using second)
        rw [same] at bound
        exact bound
      | succ i => exact ih i j (by omega) (by simpa using first) (by simpa using second)

#print axioms make_unknown_local
#print axioms make_unknown_locals
#print axioms WritableHomes.home_at
#print axioms unknown_frame_setup
#print axioms WritableHomes.ordered
end CIL.Safety
