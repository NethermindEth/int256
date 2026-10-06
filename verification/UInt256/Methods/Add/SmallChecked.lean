import UInt256.Methods.Add.SmallCarryFinish

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem small_zero_value (segment : Fin 3) (input output : Reference) (word value : BitVec 64)
    (zero : value = 0) (frame : Frame) (memory : CIL.Safety.Memory)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart (segment.val + 1))
        (smallArguments input output word) frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
        (smallArguments input output word) frame [.scalar (.i64 value)] memory = .ok (result, returned) ∧
      post result returned := by
  subst value
  exact small_zero_dispatch segment input output word frame memory post continuation

theorem SmallCarryState.increment_count {original current : CIL.Safety.Memory} {frame : Frame}
    {input output sumHome : Reference} {homes : Fin 4 → Reference}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64} (segment : Fin 3)
    (state : SmallCarryState original current frame input output sumHome homes
      (incrementedWords segment.val words) sum)
    (call : CallingConditions Extracted.program original [input] [output]) (word : BitVec 64)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      SmallCarryState original after frame input output sumHome homes
        (incrementedWords (segment.val + 1) words) sum →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
          (smallArguments input output word) frame
          [.scalar (.i64 (words ⟨segment.val + 1, by omega⟩ + 1))] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart segment.val)
        (smallArguments input output word) frame [] current = .ok (result, returned) ∧ post result returned := by
  apply state.increment call segment word post
  intro after updated
  rw [incrementedWords_next] at updated
  have value : incrementedWords segment.val words ⟨segment.val + 1, by omega⟩ =
      words ⟨segment.val + 1, by omega⟩ := by simp [incrementedWords]
  rw [value]
  exact continuation after updated

theorem small_checked (memory : CIL.Safety.Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarUInt64Index (smallArguments input output word)
        memory = .ok (final, values) ∧
      SmallResult memory final values input output word (smallOverflow memory input word) := by
  by_cases carry : inputLimb memory input 0 + word < inputLimb memory input 0
  · let post := fun final values => SmallResult memory final values input output word (smallOverflow memory input word)
    apply small_sum_invocation memory input output word call post
    intro frame entered slots tailSlots sumHome before setup layout homes saved sumSlot sumRead
    have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
    obtain ⟨references, initial⟩ := saved.carry_state (inputLimb memory input 0 + word)
      enteredWF layout homes sumSlot sumRead
    have zero : incrementedWords 0 (inputLimb memory input) = inputLimb memory input := by
      funext i
      simp [incrementedWords]
      omega
    have prepared : SmallCarryState memory before frame input output sumHome references
        (incrementedWords 0 (inputLimb memory input)) (inputLimb memory input 0 + word) := by
      rw [zero]
      exact initial
    apply small_carry_dispatch input output word (inputLimb memory input 0) frame before carry post
    apply prepared.increment_count 0 call word post
    intro first state1
    by_cases h1 : inputLimb memory input 1 + 1 = 0
    · apply small_zero_value 0 input output word _ h1 frame first post
      apply state1.increment_count 1 call word post
      intro second state2
      by_cases h2 : inputLimb memory input 2 + 1 = 0
      · apply small_zero_value 1 input output word _ h2 frame second post
        apply state2.increment_count 2 call word post
        intro third state3
        by_cases h3 : inputLimb memory input 3 + 1 = 0
        · apply small_zero_value 2 input output word _ h3 frame third post
          exact small_overflow_finish memory entered third frame input output sumHome references word
            call setup state3 carry h1 h2 h3
        · apply small_stopped_finish 2 memory entered third frame input output sumHome references word
            call setup state3 carry ?_ h3
          intro i positive bound
          have cases : i.val = 1 ∨ i.val = 2 := by omega
          rcases cases with one | two
          · have same : i = 1 := Fin.ext one
            simpa only [same] using h1
          · have same : i = 2 := Fin.ext two
            simpa only [same] using h2
      · apply small_stopped_finish 1 memory entered second frame input output sumHome references word
          call setup state2 carry ?_ h2
        intro i positive bound
        have same : i = 1 := Fin.ext (by omega)
        simpa only [same] using h1
    · exact small_stopped_finish 0 memory entered first frame input output sumHome references word
        call setup state1 carry (by intro i positive bound; omega) h1
  · have flag : smallOverflow memory input word = 0 := by simp [smallOverflow_cases, carry]
    rw [flag]
    exact small_no_carry_checked memory input output word call carry

#print axioms SmallCarryState.increment_count
#print axioms small_zero_value
#print axioms small_checked

end UInt256Proof.Safety
