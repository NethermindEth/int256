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
