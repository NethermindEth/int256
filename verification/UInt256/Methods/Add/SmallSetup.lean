import Extracted
import CIL.Safety.WordPrefix

namespace UInt256Proof.Safety

open CIL.Safety

def smallWordCount : Nat :=
  (Extracted.addScalarUInt64Body.localKinds.takeWhile (· == .word64)).length

def smallWordSpecs : List (Option (BitVec 64)) :=
  (Extracted.addScalarUInt64Body.locals.take smallWordCount).map fun value => match value with
    | .i64 word => some word
    | _ => none

def smallTailKinds := Extracted.addScalarUInt64Body.localKinds.drop smallWordCount
def smallTailValues := Extracted.addScalarUInt64Body.locals.drop smallWordCount

theorem small_local_metadata :
    Extracted.addScalarUInt64Body.localKinds = wordKinds smallWordSpecs ++ smallTailKinds ∧
    Extracted.addScalarUInt64Body.locals = wordInitializers smallWordSpecs ++ smallTailValues ∧
    InitializersFit smallTailKinds smallTailValues := by
  simp [smallWordCount, smallWordSpecs, smallTailKinds, smallTailValues,
    wordKinds, wordInitializers, InitializersFit, InitializerFits, cil_code]

/-- The extracted byte-local suffix keeps its actual type. Word homes retain
    their checked initialization and authority through creation of that suffix. -/
theorem small_frame_setup (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result slots tailSlots,
      enterFrame Extracted.addScalarUInt64Body args memory = .ok (frame, result) ∧
      frame.locals = slots ++ tailSlots ∧
      WordHomes result memory.nextIdentity smallWordSpecs slots ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨slots, tailSlots, owned, result, made, homes⟩ := make_word_prefix memory
    memory.nextIdentity smallWordSpecs smallTailKinds smallTailValues wellFormed small_local_metadata.2.2
  let frame : Frame := ⟨memory.nextIdentity, slots ++ tailSlots, owned, []⟩
  have entered : enterFrame Extracted.addScalarUInt64Body args memory = .ok (frame, result) := by
    unfold enterFrame
    dsimp only
    rw [small_local_metadata.1, small_local_metadata.2.1, made]
    simp only [Bind.bind, Except.bind, cil_code, makeArgumentHomes, Pure.pure, Except.pure, List.append_nil]
    rfl
  exact ⟨frame, result, slots, tailSlots, entered, rfl, homes,
    enterFrame_preserves_caller_memory _ _ _ _ _ entered,
    enterFrame_preserves_wellFormed _ _ _ _ _ wellFormed entered⟩

#print axioms small_local_metadata
#print axioms small_frame_setup

theorem small_word_local {memory : Memory} {lower : Nat} {frame : Frame} {slots tailSlots}
    (layout : frame.locals = slots ++ tailSlots)
    (homes : WordHomes memory lower smallWordSpecs slots)
    (index : Nat) (initial : BitVec 64)
    (specified : smallWordSpecs[index]? = some (some initial)) :
    ∃ reference, frame.locals[index]? = some (.bytes .word64 reference) ∧
      lower ≤ reference.allocation ∧
      read memory reference 8 1 = .ok (numberBytes initial.toNat 8) ∧
      access memory reference 8 1 true = .ok () := by
  obtain ⟨reference, slot, bound, loaded, writable⟩ := homes.word_at index initial specified
  have inside := (List.getElem?_eq_some_iff.mp slot).1
  exact ⟨reference, by rw [layout, List.getElem?_append_left inside]; exact slot,
    bound, loaded, writable⟩

#print axioms small_word_local

end UInt256Proof.Safety
