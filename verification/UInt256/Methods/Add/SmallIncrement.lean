import UInt256.Methods.Add.SmallSum

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

structure SmallCarryState (original current : CIL.Safety.Memory) (frame : Frame)
    (input output sumHome : Reference) (homes : Fin 4 → Reference)
    (words : Fin 4 → BitVec 64) (sum : BitVec 64) : Prop where
  call : CallingConditions Extracted.program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  slots : ∀ i : Fin 4, frame.locals[i.val]? = some (.bytes .word64 (homes i))
  reads : ∀ i, read current (homes i) 8 1 = .ok (numberBytes (words i).toNat 8)
  writes : ∀ i, access current (homes i) 8 1 true = .ok ()
  sumSlot : frame.locals[4]? = some (.bytes .word64 sumHome)
  sumRead : read current sumHome 8 1 = .ok (numberBytes sum.toNat 8)
  sumWrite : access current sumHome 8 1 true = .ok ()
  fresh : ∀ i, original.nextIdentity ≤ (homes i).allocation
  distinct : ∀ i j, i ≠ j → (homes i).allocation ≠ (homes j).allocation
  sumDistinct : ∀ i, sumHome.allocation ≠ (homes i).allocation

theorem SmallCarryState.store {original current : CIL.Safety.Memory} {frame : Frame}
    {input output sumHome : Reference} {homes : Fin 4 → Reference}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : SmallCarryState original current frame input output sumHome homes words sum)
    (call : CallingConditions Extracted.program original [input] [output])
    (index : Fin 4) (value word : BitVec 64) :
    ∃ after,
      SmallCarryState original after frame input output sumHome homes
        (fun i => if i = index then value else words i) sum ∧
      ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal index.val) pc
        (smallArguments input output word) frame (.scalar (.i64 value) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 value (state.writes index)
  have authority := write_preserves_access_below written current.nextIdentity
  have old : ∀ i, (homes i).allocation < current.nextIdentity := by
    intro i
    obtain ⟨allocation, ready⟩ := access_requirements (state.writes i)
    exact (state.call.1.1.1 _ _ ready.present).1
  obtain ⟨sumAllocation, sumReady⟩ := access_requirements state.sumWrite
  have sumOld := (state.call.1.1.1 _ _ sumReady.present).1
  have caller := state.preserved.trans (write_preserves_memory_below _ _ _ _ _ _ (state.fresh index) written)
  have afterWF := write_preserves_wellFormed _ _ _ _ _ state.call.1.1 written
  have afterWorld := write_preserves_static_world _ _ _ _ _ _ state.call.2 written
  refine ⟨after, ⟨call.after_memory_below caller afterWF afterWorld, caller, state.slots, ?_,
    fun i => authority.access (state.writes i) (old i), state.sumSlot, ?_,
    authority.access state.sumWrite sumOld, state.fresh, state.distinct, state.sumDistinct⟩, ?_⟩
  · intro i
    by_cases same : i = index
    · subst i
      simpa using loaded
    · simp only [ite_eq_right same]
      apply authority.read_eq (state.reads i) (old i)
      intro offset _
      exact write_word_outside written _ _ (Or.inl (state.distinct i index same))
  · apply authority.read_eq state.sumRead sumOld
    intro offset _
    exact write_word_outside written _ _ (Or.inl (state.sumDistinct index))
  · intro pc rest
    obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
      (body := Extracted.addScalarUInt64Body) (pc := pc) (args := smallArguments input output word)
      (rest := rest) value (state.slots index) (state.writes index)
    rw [written] at sameWrite
    cases sameWrite
    exact stepped

theorem SmallSaved.carry_state {original entered current : CIL.Safety.Memory}
    {frame : Frame} {input output sumHome : Reference} {slots tailSlots : List LocalSlot}
    (saved : SmallSaved original entered current input output slots 4)
    (sum : BitVec 64)
    (enteredWF : entered.WellFormed)
    (layout : frame.locals = slots ++ tailSlots)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs slots)
    (sumSlot : frame.locals[4]? = some (.bytes .word64 sumHome))
    (sumRead : read current sumHome 8 1 = .ok (numberBytes sum.toNat 8)) :
    ∃ references : Fin 4 → Reference,
      SmallCarryState original current frame input output sumHome references (inputLimb original input) sum := by
  have candidates := fun i : Fin 4 => saved.completed i i.isLt
  let references : Fin 4 → Reference := fun i => Classical.choose (candidates i)
  have facts := fun i : Fin 4 => Classical.choose_spec (candidates i)
  have originalWrites : ∀ i, access entered (references i) 8 1 true = .ok () := by
    intro i
    obtain ⟨reference, slot, _, _, writable⟩ := homes.word_at i.val 0 (small_input_spec i)
    have same : reference = references i := by rw [(facts i).1] at slot; simpa using slot.symm
    simpa only [same] using writable
  have sumSpec : smallWordSpecs[4]? = some (some 0) := by
    simp [smallWordSpecs, smallWordCount, cil_code]
  have sumInside : 4 < slots.length := by
    rw [homes.length]
    exact (List.getElem?_eq_some_iff.mp sumSpec).1
  have sumPrefix : slots[4]? = some (.bytes .word64 sumHome) := by
    simpa only [layout, List.getElem?_append_left sumInside] using sumSlot
  obtain ⟨sumReference, foundSum, _, _, sumWritable⟩ := homes.word_at 4 0 sumSpec
  have sameSum : sumReference = sumHome := by rw [sumPrefix] at foundSum; simpa using foundSum.symm
  subst sumReference
  obtain ⟨sumAllocation, sumReady⟩ := access_requirements sumWritable
  refine ⟨references, ⟨saved.call, saved.preserved, ?_, fun i => (facts i).2.2,
    ?_, sumSlot, sumRead, saved.authority.access sumWritable (enteredWF.1 _ _ sumReady.present).1,
    ?_, ?_, ?_⟩⟩
  · intro i
    have inside := (List.getElem?_eq_some_iff.mp (facts i).1).1
    rw [layout, List.getElem?_append_left inside]
    exact (facts i).1
  · intro i
    exact saved.authority.access (originalWrites i) (facts i).2.1
  · intro i
    exact homes.word_bound i.val (references i) (facts i).1
  · intro i j different
    have differentVal : i.val ≠ j.val := fun h => different (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne differentVal with before | after
    · exact Nat.ne_of_lt (homes.ordered i.val j.val _ _ before (facts i).1 (facts j).1)
    · exact Ne.symm (Nat.ne_of_lt (homes.ordered j.val i.val _ _ after (facts j).1 (facts i).1))
  · intro i
    exact Ne.symm (Nat.ne_of_lt (homes.ordered i.val 4 _ _ i.isLt (facts i).1 sumPrefix))

#print axioms SmallCarryState.store
#print axioms SmallSaved.carry_state

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

def smallIncrementStart : Nat → Nat
  | 0 => match Extracted.addScalarUInt64Body.code[smallCarryDecision]? with
      | some (.bltu target) => target
      | _ => 0
  | n + 1 => ((Extracted.addScalarUInt64Body.code.drop (smallIncrementStart n)).findSome? fun op =>
      match op with | .brzero target => some target | _ => none).getD 0

def smallIncrementDecision (segment : Nat) : Nat :=
  smallIncrementStart segment +
    (Extracted.addScalarUInt64Body.code.drop (smallIncrementStart segment)).findIdx fun op =>
      match op with | .brzero _ => true | _ => false

theorem small_increment_prefix (segment : Fin 3) (input output home : Reference) (word value : BitVec 64)
    (frame : Frame) (before after : CIL.Safety.Memory)
    (slot : frame.locals[segment.val + 1]? = some (.bytes .word64 home))
    (loaded : read before home 8 1 = .ok (numberBytes value.toNat 8))
    (stored : ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal (segment.val + 1)) pc
      (smallArguments input output word) frame (.scalar (.i64 (value + 1)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
        (smallArguments input output word) frame [.scalar (.i64 (value + 1))] after = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart segment.val)
        (smallArguments input output word) frame [] before = .ok (result, returned) ∧
      post result returned := by
  have reading := load_local_word64_of_read loaded
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    conv in (smallIncrementStart _) => cbv
    conv at continuation in (smallIncrementDecision _) => cbv
    dsimp at slot stored
    repeat'
      first
      | exact continuation
      | simp (config := { failIfUnchanged := false })
        apply run_next_exists post
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · first
          | exact stored _ _
          | simp (config := { implicitDefEqProofs := false })
              [cil_code, step, slot, reading, checkedValue, numericValue, pureArity, scalars,
                CIL.step, CIL.binary, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem SmallCarryState.increment {original current : CIL.Safety.Memory} {frame : Frame}
    {input output sumHome : Reference} {homes : Fin 4 → Reference}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : SmallCarryState original current frame input output sumHome homes words sum)
    (call : CallingConditions Extracted.program original [input] [output])
    (segment : Fin 3) (word : BitVec 64)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      SmallCarryState original after frame input output sumHome homes
        (fun i => if i = (⟨segment.val + 1, by omega⟩ : Fin 4) then words i + 1 else words i) sum →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
          (smallArguments input output word) frame
          [.scalar (.i64 (words ⟨segment.val + 1, by omega⟩ + 1))] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart segment.val)
        (smallArguments input output word) frame [] current = .ok (result, returned) ∧ post result returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  obtain ⟨after, updated, stored⟩ := state.store call index (words index + 1) word
  have shape : (fun i => if i = index then words index + 1 else words i) =
      (fun i => if i = index then words i + 1 else words i) := by
    funext i
    by_cases same : i = index
    · subst i; rfl
    · simp [same]
  rw [shape] at updated
  exact small_increment_prefix segment input output (homes index) word (words index) frame current after
    (state.slots index) (state.reads index) stored post (continuation after updated)

#print axioms small_increment_prefix
#print axioms SmallCarryState.increment

end UInt256Proof.Safety
