import CIL.Safety.UnknownHomes
import CIL.Safety.NumericLocals
import CIL.Safety.AccessBelow

namespace CIL.Safety

/-- Only words established by actual writes or checked helper results may be
    loaded. A missing entry grants no initialization or value fact. -/
def WordSnapshots (memory : Memory) (slots : List LocalSlot)
    (known : Nat → Option (BitVec 64)) : Prop :=
  ∀ index value, known index = some value →
    ∃ reference, slots[index]? = some (.bytes .word64 reference) ∧
      read memory reference 8 1 = .ok (numberBytes value.toNat 8)

def rememberWord (known : Nat → Option (BitVec 64)) (index : Nat) (value : BitVec 64) :
    Nat → Option (BitVec 64) := fun other => if other = index then some value else known other

theorem WordSnapshots.empty (memory : Memory) (slots : List LocalSlot) :
    WordSnapshots memory slots (fun _ => none) := by
  intro index value impossible
  cases impossible

theorem WritableHomes.distinct {memory : Memory} {lower : Nat} {kinds slots}
    (homes : WritableHomes memory lower kinds slots) (i j : Nat)
    (leftKind rightKind : CIL.LocalKind) (left right : Reference)
    (different : i ≠ j) (first : slots[i]? = some (.bytes leftKind left))
    (second : slots[j]? = some (.bytes rightKind right)) : left.allocation ≠ right.allocation := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · exact Nat.ne_of_lt (homes.ordered i j leftKind rightKind left right before first second)
  · exact Nat.ne_of_gt (homes.ordered j i rightKind leftKind right left after second first)

/-- A helper's checked readback and memory effect update one snapshot while
    preserving every other private word, including across nested frame allocation. -/
theorem WordSnapshots.after_effect {entered before after : Memory} {boundary : Nat} {kinds slots}
    {known : Nat → Option (BitVec 64)} (snapshots : WordSnapshots before slots known)
    (homes : WritableHomes entered boundary kinds slots) (wf : before.WellFormed)
    (index : Nat) (reference : Reference) (value : BitVec 64)
    (slot : slots[index]? = some (.bytes .word64 reference))
    (loaded : read after reference 8 1 = .ok (numberBytes value.toNat 8))
    (authority : AccessBelow before.nextIdentity before after)
    (outside : ∀ id, id < before.nextIdentity → id ≠ reference.allocation → ∀ offset,
      after.cells id offset = before.cells id offset) :
    WordSnapshots after slots (rememberWord known index value) := by
  intro other word specified
  by_cases same : other = index
  · subst other
    have sameWord : value = word := by simpa [rememberWord] using specified
    subst word
    exact ⟨reference, slot, loaded⟩
  · have previous : known other = some word := by simpa [rememberWord, same] using specified
    obtain ⟨r, found, readable⟩ := snapshots other word previous
    have ready : access before r 8 1 false = .ok () := by
      unfold read at readable
      cases h : access before r 8 1 false with
      | error fault => simp [h, Bind.bind, Except.bind] at readable
      | ok result => cases result; rfl
    obtain ⟨allocation, requirements⟩ := access_requirements ready
    have old := (wf.1 _ _ requirements.present).1
    have disjoint := homes.distinct other index .word64 .word64 r reference same found slot
    exact ⟨r, found, authority.read_eq readable old (fun offset _ => outside r.allocation old disjoint _)⟩

theorem WordSnapshots.after_write {entered before after : Memory} {boundary : Nat} {kinds slots}
    {known : Nat → Option (BitVec 64)} (snapshots : WordSnapshots before slots known)
    (homes : WritableHomes entered boundary kinds slots) (wf : before.WellFormed)
    (index : Nat) (reference : Reference) (value : BitVec 64)
    (slot : slots[index]? = some (.bytes .word64 reference))
    (written : write before reference (numberBytes value.toNat 8) 1 = .ok after) :
    WordSnapshots after slots (rememberWord known index value) := by
  have readback := write_readback _ _ _ _ _ written
  have length : (numberBytes value.toNat 8).length = 8 := by simp [numberBytes]
  rw [length] at readback
  exact snapshots.after_effect homes wf index reference value slot readback
    (write_preserves_access_below written _) (fun id _ different offset =>
      write_outside _ _ _ _ _ id offset written (Or.inl different))

/-- Checked local reads consume the remembered initialization and value. -/
theorem WordSnapshots.load {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {known : Nat → Option (BitVec 64)}
    (snapshots : WordSnapshots memory frame.locals known) (value : BitVec 64)
    (specified : known index = some value) :
    step body (.local index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar (.i64 value) :: stack) frame memory) := by
  obtain ⟨reference, slot, loaded⟩ := snapshots index value specified
  exact step_load_numeric_local .word64 (.i64 value) value.toNat rfl slot loaded

/-- Writing a word initializes precisely that home and retains the caller's
    bytes and the other remembered locals. No prior read permission is needed. -/
theorem WordSnapshots.store {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {entered memory : Memory} {boundary : Nat} {kinds}
    {known : Nat → Option (BitVec 64)}
    (snapshots : WordSnapshots memory frame.locals known)
    (homes : WritableHomes entered boundary kinds frame.locals) (wf : memory.WellFormed)
    (reference : Reference) (value : BitVec 64)
    (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (ready : access memory reference 8 1 true = .ok ()) :
    ∃ after,
      step body (.setLocal index) pc args frame (.scalar (.i64 value) :: stack) memory =
        .ok (.next (pc + 1) stack frame after) ∧
      WordSnapshots after frame.locals (rememberWord known index value) ∧ after.WellFormed ∧
      MemoryBelow boundary memory after ∧ AccessBelow memory.nextIdentity memory after ∧
      write memory reference (numberBytes value.toNat 8) 1 = .ok after := by
  obtain ⟨after, stepped, written, _⟩ := step_store_numeric_local
    (body := body) (pc := pc) (args := args) (rest := stack)
    .word64 (.i64 value) value.toNat rfl slot ready
  exact ⟨after, stepped, snapshots.after_write homes wf index reference value slot written,
    write_preserves_wellFormed _ _ _ _ _ wf written,
    write_preserves_memory_below _ _ _ _ _ _ (homes.home_bound index .word64 reference slot) written,
    write_preserves_access_below written _, written⟩

#print axioms WordSnapshots.after_effect
#print axioms WordSnapshots.after_write
#print axioms WordSnapshots.load
#print axioms WordSnapshots.store
end CIL.Safety
