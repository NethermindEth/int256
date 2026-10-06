import Extracted
import CIL.Safety.StepComposition
import CIL.Safety.WordLocals
import CIL.Safety.WordPrefix
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow

namespace UInt256Proof.Safety

open CIL.Safety

def smallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

/-- Locate the first use of the saved low limb. Disabled hardware instructions
    are excluded by extraction; a scalar-only helper needs no feature branch. -/
def smallScalarStart : Nat :=
  Extracted.addScalarUInt64Body.code.findIdx fun op => match op with
    | .local 0 => true
    | _ => false

theorem small_input_prefix (input output : Reference) (word : BitVec 64)
    (words : Fin 4 → BitVec 64) (frame : Frame) (states : Nat → Memory)
    (formed : ∀ i : Fin 4, form (states i.val) input = .ok input)
    (loads : ∀ (i : Fin 4) rest,
      instruction (.field i) (.reference (.address input) :: rest) (states i.val) =
        .ok (states i.val, .scalar (.i64 (words i)) :: rest))
    (stores : ∀ (i : Fin 4) pc rest,
      step Extracted.addScalarUInt64Body (.setLocal i.val) pc (smallArguments input output word)
        frame (.scalar (.i64 (words i)) :: rest) (states i.val) =
          .ok (.next (pc + 1) rest frame (states (i.val + 1))))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index smallScalarStart
        (smallArguments input output word) frame [] (states 4) = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (smallArguments input output word) frame [] (states 0) = .ok (result, returned) ∧
      post result returned := by
  conv at continuation in smallScalarStart => cbv
  have f0 := formed 0
  have f1 := formed 1
  have f2 := formed 2
  have f3 := formed 3
  have l0 := loads 0
  have l1 := loads 1
  have l2 := loads 2
  have l3 := loads 3
  have s0 := stores 0
  have s1 := stores 1
  have s2 := stores 2
  have s3 := stores 3
  dsimp at f0 f1 f2 f3 l0 l1 l2 l3 s0 s1 s2 s3
  simp only [show (3 : Fin 4).val = 3 from rfl] at f3 l3 s3
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · first
        | exact s0 _ _
        | exact s1 _ _
        | exact s2 _ _
        | exact s3 _ _
        | simp (config := { implicitDefEqProofs := false })
            [smallArguments, cil_code, step, checkedValue, numericValue, formValue,
              f0, f1, f2, f3, l0, l1, l2, l3, pureArity, scalars, CIL.step,
              CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms small_input_prefix

end UInt256Proof.Safety

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

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- A private word store retains the original caller snapshot and all existing
    frame access authority. It can be repeated for each operand limb. -/
theorem small_private_store (original entered current : CIL.Safety.Memory)
    (input output : Reference) (word value : BitVec 64) (frame : Frame) (slots tailSlots)
    (call : CallingConditions Extracted.program original [input] [output])
    (currentCall : CallingConditions Extracted.program current [input] [output])
    (enteredWF : entered.WellFormed)
    (layout : frame.locals = slots ++ tailSlots)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs slots)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (initial : BitVec 64)
    (specified : smallWordSpecs[index]? = some (some initial)) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes .word64 reference) ∧
      read after reference 8 1 = .ok (numberBytes value.toNat 8) ∧
      MemoryBelow original.nextIdentity original after ∧
      CallingConditions Extracted.program after [input] [output] ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes value.toNat 8) 1 = .ok after ∧
      ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal index) pc
        (smallArguments input output word) frame (.scalar (.i64 value) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := small_word_local layout homes index initial specified
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have old := (enteredWF.1 reference.allocation allocation ready.present).1
  have permitted := authority.access writable old
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 value permitted
  have caller := preserved.trans (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have afterWF := write_preserves_wellFormed _ _ _ _ _ currentCall.1.1 written
  have afterWorld := write_preserves_static_world _ _ _ _ _ _ currentCall.2 written
  refine ⟨reference, after, slot, loaded, caller,
    call.after_memory_below caller afterWF afterWorld,
    authority.trans (write_preserves_access_below written _), written, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := Extracted.addScalarUInt64Body) (pc := pc)
    (args := smallArguments input output word) (rest := rest) value slot permitted
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

#print axioms small_private_store

end UInt256Proof.Safety
