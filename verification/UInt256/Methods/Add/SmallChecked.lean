import UInt256.Methods.Add.SmallCarryBranch
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Safety

open UInt256Model.Safety

def incrementedWords (count : Nat) (words : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 :=
  fun i => if 0 < i.val ∧ i.val ≤ count then words i + 1 else words i

theorem incrementedWords_next (segment : Fin 3) (words : Fin 4 → BitVec 64) :
    (fun i => if i = (⟨segment.val + 1, by omega⟩ : Fin 4)
      then incrementedWords segment.val words i + 1 else incrementedWords segment.val words i) =
      incrementedWords (segment.val + 1) words := by
  obtain ⟨n, bound⟩ := segment
  have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp [incrementedWords]

theorem small_stopped_words (segment : Fin 3) (words : Fin 4 → BitVec 64) (word : BitVec 64)
    (carry : words 0 + word < words 0)
    (previous : ∀ i : Fin 4, 0 < i.val → i.val ≤ segment.val → words i + 1 = 0)
    (stop : words ⟨segment.val + 1, by omega⟩ + 1 ≠ 0) :
    smallCarryOutput segment.val (words 0 + word) (incrementedWords (segment.val + 1) words) =
      UInt256Proof.smallResult words word := by
  have p1 := previous 1
  have p2 := previous 2
  simp only [BitVec.ofNat_eq_ofNat] at p1 p2 stop
  obtain ⟨n, bound⟩ := segment
  have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp at p1 p2 stop
    funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [smallCarryOutput, incrementedWords, UInt256Proof.smallResult, carry, p1, p2, stop]

theorem small_overflow_words (words : Fin 4 → BitVec 64) (word : BitVec 64)
    (carry : words 0 + word < words 0)
    (first : words 1 + 1 = 0) (second : words 2 + 1 = 0) (third : words 3 + 1 = 0) :
    (fun i : Fin 4 => if i.val = 0 then words 0 + word else 0) = UInt256Proof.smallResult words word := by
  simp only [BitVec.ofNat_eq_ofNat] at first second third
  funext ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [UInt256Proof.smallResult, carry, first, second, third]

theorem small_result_value (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference) (word : BitVec 64) :
    UInt256Model.value (UInt256Proof.smallResult (inputLimb memory input) word) =
      inputValue memory input + BitVec.ofNat 256 word.toNat := by
  rw [UInt256Proof.small_result_sum]
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [initial]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

def smallOverflow (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference) (word : BitVec 64) : BitVec 32 :=
  if 2^256 ≤ (inputValue memory input).toNat + word.toNat then 1 else 0

theorem smallOverflow_cases (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference) (word : BitVec 64) :
    smallOverflow memory input word =
      if inputLimb memory input 0 + word < inputLimb memory input 0 ∧
        inputLimb memory input 1 + 1 = 0 ∧ inputLimb memory input 2 + 1 = 0 ∧
        inputLimb memory input 3 + 1 = 0 then 1 else 0 := by
  have overflow := UInt256Proof.Reporting.small_overflow_iff (inputLimb memory input) word
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  have wideBound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
  rw [initial] at overflow
  simp [UInt256Model.value, UInt256Proof.singleLimb, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt wideBound] at overflow
  unfold smallOverflow
  simp only [BitVec.ofNat_eq_ofNat, Nat.reducePow, ← overflow]

#print axioms incrementedWords_next
#print axioms small_stopped_words
#print axioms small_overflow_words
#print axioms small_result_value
#print axioms smallOverflow_cases

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem small_stopped_finish (segment : Fin 3) (original entered current : CIL.Safety.Memory)
    (frame : Frame) (input output sumHome : Reference) (homes : Fin 4 → Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (smallArguments input output word) original =
      .ok (frame, entered))
    (state : SmallCarryState original current frame input output sumHome homes
      (incrementedWords (segment.val + 1) (inputLimb original input)) (inputLimb original input 0 + word))
    (carry : inputLimb original input 0 + word < inputLimb original input 0)
    (previous : ∀ i : Fin 4, 0 < i.val → i.val ≤ segment.val → inputLimb original input i + 1 = 0)
    (stop : inputLimb original input ⟨segment.val + 1, by omega⟩ + 1 ≠ 0) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
        (smallArguments input output word) frame
        [.scalar (.i64 (inputLimb original input ⟨segment.val + 1, by omega⟩ + 1))] current =
          .ok (final, values) ∧ SmallResult original final values input output word (smallOverflow original input word) := by
  let words := smallCarryOutput segment.val (inputLimb original input 0 + word)
    (incrementedWords (segment.val + 1) (inputLimb original input))
  have math : UInt256Model.value words = inputValue original input + BitVec.ofNat 256 word.toNat :=
    (congrArg UInt256Model.value (small_stopped_words segment (inputLimb original input) word carry previous stop)).trans
      (small_result_value original input word)
  have atIndex : incrementedWords (segment.val + 1) (inputLimb original input)
      ⟨segment.val + 1, by omega⟩ = inputLimb original input ⟨segment.val + 1, by omega⟩ + 1 := by
    simp [incrementedWords]
  have flag : smallOverflow original input word = 0 := by
    rw [smallOverflow_cases]
    simp only [BitVec.ofNat_eq_ofNat] at stop
    obtain ⟨n, bound⟩ := segment
    have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals dsimp at stop
    all_goals simp [stop]
  let post := fun final values => SmallResult original final values input output word (smallOverflow original input word)
  have execution := state.nonzero_prefix segment word (by rw [atIndex]; exact stop) post
  rw [atIndex] at execution
  apply execution
  have finished := small_store_finish ⟨segment.val + 1, by omega⟩ original entered current frame
    input output word words call setup state.call state.preserved.cells math
  have notOverflow : segment.val + 1 ≠ 4 := by omega
  simpa [post, words, smallCarryOutput, smallBranchFlag, notOverflow, flag] using finished

theorem small_overflow_finish (original entered current : CIL.Safety.Memory)
    (frame : Frame) (input output sumHome : Reference) (homes : Fin 4 → Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (smallArguments input output word) original =
      .ok (frame, entered))
    (state : SmallCarryState original current frame input output sumHome homes
      (incrementedWords 3 (inputLimb original input)) (inputLimb original input 0 + word))
    (carry : inputLimb original input 0 + word < inputLimb original input 0)
    (first : inputLimb original input 1 + 1 = 0)
    (second : inputLimb original input 2 + 1 = 0)
    (third : inputLimb original input 3 + 1 = 0) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart 3)
        (smallArguments input output word) frame [] current = .ok (final, values) ∧
      SmallResult original final values input output word (smallOverflow original input word) := by
  let words := fun i : Fin 4 => if i.val = 0 then inputLimb original input 0 + word else 0
  have math : UInt256Model.value words = inputValue original input + BitVec.ofNat 256 word.toNat :=
    (congrArg UInt256Model.value (small_overflow_words (inputLimb original input) word carry first second third)).trans
      (small_result_value original input word)
  have flag : smallOverflow original input word = 1 := by
    rw [smallOverflow_cases]
    simp only [BitVec.ofNat_eq_ofNat] at first second third
    simp [carry, first, second, third]
  apply state.overflow_prefix word
    (fun final values => SmallResult original final values input output word (smallOverflow original input word))
  have finished := small_store_finish 4 original entered current frame input output word words
    call setup state.call state.preserved.cells math
  simpa [words, smallBranchFlag, show (3 : Fin 4).val = 3 from rfl,
    show (4 : Fin 5).val = 4 from rfl, flag] using finished

#print axioms small_stopped_finish
#print axioms small_overflow_finish

end UInt256Proof.Safety

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
