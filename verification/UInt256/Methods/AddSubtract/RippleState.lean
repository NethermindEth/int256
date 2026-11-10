import UInt256.Safety.PrivateCalls
import CIL.Safety.LocalCalls

/-! Four-limb carry and borrow callers share private-home and completed-result evidence. -/

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Exactly the completed result locals have known contents; unwritten results remain unknown. -/
def completedLocals (words : Fin 4 → BitVec 64) (base done : Nat) : Nat → Option CIL.Value :=
  fun index => if known : base ≤ index ∧ index - base < 4 ∧ index - base < done then
    some (.i64 (words ⟨index - base, known.2.1⟩)) else none

/-- Adding the next completed result remembers precisely its local. -/
theorem completedLocals_next (words : Fin 4 → BitVec 64) (base : Nat) (index : Fin 4) :
    rememberLocal (completedLocals words base index.val) (index.val + base) (.i64 (words index)) =
      completedLocals words base (index.val + 1) := by
  funext other
  by_cases same : other = index.val + base
  · subst other
    simp [rememberLocal, completedLocals, index.isLt]
  · have different : base ≤ other → other - base ≠ index.val := by omega
    simp only [rememberLocal, same, ↓reduceIte, completedLocals]
    by_cases lower : base ≤ other
    · have before : other - base < index.val + 1 ↔ other - base < index.val := by
        have := different lower
        omega
      simp [lower, before]
    · simp [lower]

/-- Caller views, private flag authority and initialized result locals for a ripple operation. -/
structure RippleState (program : CIL.Program) (original current : Memory) (frame : Frame)
    (left right output flagHome : Reference) (results : Fin 4 → Reference)
    (flags : Nat → BitVec 64) (words : Fin 4 → BitVec 64)
    (done flagIndex resultBase : Nat) : Prop where
  call : CallingConditions program current [left, right] [output]
  inputBytes : ∀ reference ∈ [left, right],
    (fun offset => (current.cells reference.allocation offset).bits) =
      (fun offset => (original.cells reference.allocation offset).bits)
  flagSlot : frame.locals[flagIndex]? = some (.bytes .word64 flagHome)
  resultSlots : ∀ i, frame.locals[i.val + resultBase]? = some (.bytes .word64 (results i))
  flagWrite : access current flagHome 8 1 true = .ok ()
  resultWrites : ∀ i, access current (results i) 8 1 true = .ok ()
  flagRead : read current flagHome 8 1 = .ok (numberBytes (flags done).toNat 8)
  flagBound : (flags done).toNat ≤ 1
  callerSeparate : ∀ reference ∈ [left, right],
    reference.allocation ≠ flagHome.allocation ∧ ∀ i, reference.allocation ≠ (results i).allocation
  flagSeparate : ∀ i, (results i).allocation ≠ flagHome.allocation
  resultSeparate : ∀ i j, i ≠ j → (results i).allocation ≠ (results j).allocation
  flagFresh : original.nextIdentity ≤ flagHome.allocation
  resultsFresh : ∀ i, original.nextIdentity ≤ (results i).allocation
  callerCells : ∀ id, id < original.nextIdentity → ∀ offset,
    current.cells id offset = original.cells id offset
  snapshots : LocalSnapshots current frame.locals (completedLocals words resultBase done)

/-- Both helper outputs replace their old contents; earlier results are apart from both writes. -/
theorem RippleState.advance {program original before after frame left right output flagHome
    results flags words flagIndex resultBase} (index : Fin 4)
    (state : RippleState program original before frame left right output flagHome results
      flags words index.val flagIndex resultBase)
    (flagRead : read after flagHome 8 1 = .ok (numberBytes (flags (index.val + 1)).toNat 8))
    (flagBound : (flags (index.val + 1)).toNat ≤ 1)
    (resultRead : read after (results index) 8 1 = .ok (numberBytes (words index).toNat 8))
    (formed : after.WellFormed) (world : StaticWorldPreserved program before after)
    (framed : Confined [(flagHome, 8), (results index, 8)] before after) :
    RippleState program original after frame left right output flagHome results
      flags words (index.val + 1) flagIndex resultBase := by
  have separate : ∀ reference ∈ [left, right],
      reference.allocation ≠ flagHome.allocation ∧
        reference.allocation ≠ (results index).allocation :=
    fun reference member =>
      ⟨(state.callerSeparate reference member).1, (state.callerSeparate reference member).2 index⟩
  have flagOld := state.call.1.1.access_bound state.flagWrite
  have resultOld := fun i => state.call.1.1.access_bound (state.resultWrites i)
  refine ⟨private_calling_conditions framed formed world state.call separate, ?_,
    state.flagSlot, state.resultSlots, (framed.access_write _ flagOld _ _).trans state.flagWrite,
    fun i => (framed.access_write _ (resultOld i) _ _).trans (state.resultWrites i),
    flagRead, flagBound, state.callerSeparate, state.flagSeparate, state.resultSeparate,
    state.flagFresh, state.resultsFresh, ?_, ?_⟩
  · intro reference member
    exact (private_input_bytes framed state.call member (separate reference member).1
      (separate reference member).2).trans (state.inputBytes reference member)
  · intro id old offset
    have belowFlag := Nat.lt_of_lt_of_le old state.flagFresh
    have belowResult := Nat.lt_of_lt_of_le old (state.resultsFresh index)
    exact (framed.cells_apart (Nat.lt_trans belowFlag flagOld)
      (by simp [Nat.ne_of_lt belowFlag, Nat.ne_of_lt belowResult]) offset).trans
      (state.callerCells id old offset)
  · rw [← completedLocals_next]
    apply state.snapshots.after_helper_write state.call.1.1 framed (index.val + resultBase)
      .word64 (results index) (.i64 (words index)) _ (state.resultSlots index) rfl resultRead
    intro other value kind home different specified slot
    unfold completedLocals at specified
    split at specified
    next known =>
      let previous : Fin 4 := ⟨other - resultBase, known.2.1⟩
      have position : previous.val + resultBase = other := Nat.sub_add_cancel known.1
      have actual := state.resultSlots previous
      rw [position, slot] at actual
      obtain ⟨rfl, rfl⟩ := LocalSlot.bytes.inj (Option.some.inj actual)
      have distinct : previous ≠ index := by
        intro same
        exact different (by simpa [same] using position.symm)
      simp [Apart, state.flagSeparate previous, state.resultSeparate previous index distinct]
    next impossible => simp at specified

end UInt256Proof.AddSubtract.Safety
