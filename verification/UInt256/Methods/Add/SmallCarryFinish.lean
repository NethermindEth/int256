import UInt256.Methods.Add.SmallCarryArithmetic

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
