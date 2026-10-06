import UInt256.Methods.Add.SmallSaved

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

def smallCarryDecision : Nat :=
  Extracted.addScalarUInt64Body.code.findIdx fun op => match op with
    | .bltu _ => true
    | _ => false

theorem small_sum_prefix (input output lowHome sumHome : Reference) (word low : BitVec 64)
    (frame : Frame) (before after : CIL.Safety.Memory)
    (lowSlot : frame.locals[0]? = some (.bytes .word64 lowHome))
    (sumSlot : frame.locals[4]? = some (.bytes .word64 sumHome))
    (lowBefore : read before lowHome 8 1 = .ok (numberBytes low.toNat 8))
    (lowAfter : read after lowHome 8 1 = .ok (numberBytes low.toNat 8))
    (sumAfter : read after sumHome 8 1 = .ok (numberBytes (low + word).toNat 8))
    (stored : ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal 4) pc
      (smallArguments input output word) frame (.scalar (.i64 (low + word)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index smallCarryDecision
        (smallArguments input output word) frame
        [.scalar (.i64 low), .scalar (.i64 (low + word))] after = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index smallScalarStart
        (smallArguments input output word) frame [] before = .ok (result, returned) ∧
      post result returned := by
  conv in smallScalarStart => cbv
  conv at continuation in smallCarryDecision => cbv
  have r0 := load_local_word64_of_read lowBefore
  have r1 := load_local_word64_of_read lowAfter
  have r4 := load_local_word64_of_read sumAfter
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
            [cil_code, smallArguments, step, lowSlot, sumSlot, r0, r1, r4, checkedValue,
              numericValue, pureArity, scalars, CIL.step, CIL.binary,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem SmallSaved.sum_store {original entered current : CIL.Safety.Memory}
    {input output : Reference} {slots tailSlots : List LocalSlot} {frame : Frame}
    (state : SmallSaved original entered current input output slots 4)
    (word : BitVec 64)
    (call : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (layout : frame.locals = slots ++ tailSlots)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs slots) :
    ∃ sumHome after,
      SmallSaved original entered after input output slots 4 ∧
      frame.locals[4]? = some (.bytes .word64 sumHome) ∧
      read after sumHome 8 1 = .ok (numberBytes (inputLimb original input 0 + word).toNat 8) ∧
      ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal 4) pc
        (smallArguments input output word) frame
        (.scalar (.i64 (inputLimb original input 0 + word)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  have specified : smallWordSpecs[4]? = some (some 0) := by
    simp [smallWordSpecs, smallWordCount, cil_code]
  obtain ⟨reference, after, fullSlot, loaded, preserved, afterCall, authority, written, stepped⟩ :=
    small_private_store original entered current input output word (inputLimb original input 0 + word)
      frame slots tailSlots call state.call enteredWF layout homes state.preserved state.authority 4 0 specified
  have inside : 4 < slots.length := by
    rw [homes.length]
    exact (List.getElem?_eq_some_iff.mp specified).1
  have slot : slots[4]? = some (.bytes .word64 reference) := by
    simpa only [layout, List.getElem?_append_left inside] using fullSlot
  refine ⟨reference, after, ⟨afterCall, preserved, authority, ?_⟩, fullSlot, loaded, stepped⟩
  intro i earlier
  obtain ⟨previous, previousSlot, previousOld, previousRead⟩ := state.completed i earlier
  have different := Nat.ne_of_lt (homes.ordered i.val 4 previous reference earlier previousSlot slot)
  refine ⟨previous, previousSlot, previousOld,
    (write_preserves_access_below written entered.nextIdentity).read_eq previousRead previousOld ?_⟩
  intro offset _
  exact write_word_outside written _ _ (Or.inl different)

#print axioms small_sum_prefix
#print axioms SmallSaved.sum_store

theorem small_sum_invocation (memory : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output])
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ frame entered slots tailSlots sumHome after,
      enterFrame Extracted.addScalarUInt64Body (smallArguments input output word) memory =
        .ok (frame, entered) →
      frame.locals = slots ++ tailSlots →
      WordHomes entered memory.nextIdentity smallWordSpecs slots →
      SmallSaved memory entered after input output slots 4 →
      frame.locals[4]? = some (.bytes .word64 sumHome) →
      read after sumHome 8 1 = .ok (numberBytes (inputLimb memory input 0 + word).toNat 8) →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index smallCarryDecision
          (smallArguments input output word) frame
          [.scalar (.i64 (inputLimb memory input 0)), .scalar (.i64 (inputLimb memory input 0 + word))]
          after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      invoke Extracted.program fuel Extracted.addScalarUInt64Index (smallArguments input output word)
        memory = .ok (result, returned) ∧ post result returned := by
  apply small_saved_invocation memory input output word call post
  intro frame entered slots tailSlots before setup layout homes saved
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  obtain ⟨sumHome, after, updated, sumSlot, sumRead, stored⟩ :=
    saved.sum_store word call enteredWF layout homes
  obtain ⟨lowHome, lowSlot, _, lowBefore⟩ := saved.completed 0 (by decide)
  obtain ⟨afterHome, afterSlot, _, lowAfter⟩ := updated.completed 0 (by decide)
  have same : afterHome = lowHome := by rw [lowSlot] at afterSlot; simpa using afterSlot.symm
  subst afterHome
  have fullSlot : frame.locals[0]? = some (.bytes .word64 lowHome) := by
    have inside : 0 < slots.length := (List.getElem?_eq_some_iff.mp lowSlot).1
    rw [layout, List.getElem?_append_left inside]
    exact lowSlot
  exact small_sum_prefix input output lowHome sumHome word (inputLimb memory input 0)
    frame before after fullSlot sumSlot lowBefore lowAfter sumRead stored post
    (continuation frame entered slots tailSlots sumHome after setup layout homes updated sumSlot sumRead)

#print axioms small_sum_invocation

end UInt256Proof.Safety
