import UInt256.Methods.Add.SmallIncrement
import UInt256.Methods.Add.SmallFinish

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

def smallCarryOutput (segment : Nat) (sum : BitVec 64) (words : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 :=
  fun i => if i.val = 0 then sum else if i.val ≤ segment then 0 else words i

theorem small_carry_dispatch (input output : Reference) (word low : BitVec 64)
    (frame : Frame) (memory : CIL.Safety.Memory) (carry : low + word < low)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart 0)
        (smallArguments input output word) frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index smallCarryDecision
        (smallArguments input output word) frame [.scalar (.i64 low), .scalar (.i64 (low + word))]
        memory = .ok (result, returned) ∧ post result returned := by
  conv in smallCarryDecision => cbv
  conv at continuation in (smallIncrementStart _) => cbv
  apply run_next_exists post
  · simp only [cil_code]; rfl
  · simp only [cil_code]; rfl
  · simp [step, numericValue, pureArity, scalars, CIL.step, carry,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exact continuation

theorem small_zero_dispatch (segment : Fin 3) (input output : Reference) (word : BitVec 64)
    (frame : Frame) (memory : CIL.Safety.Memory)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart (segment.val + 1))
        (smallArguments input output word) frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
        (smallArguments input output word) frame [.scalar (.i64 0)] memory = .ok (result, returned) ∧
      post result returned := by
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    conv in (smallIncrementDecision _) => cbv
    conv at continuation in (smallIncrementStart _) => cbv
    apply run_next_exists post
    · simp only [cil_code]; rfl
    · simp only [cil_code]; rfl
    · simp [step, numericValue, pureArity, scalars, CIL.step, CIL.truth,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · exact continuation

theorem SmallCarryState.nonzero_prefix {original current : CIL.Safety.Memory} {frame : Frame}
    {input output sumHome : Reference} {homes : Fin 4 → Reference}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : SmallCarryState original current frame input output sumHome homes words sum)
    (segment : Fin 3) (word : BitVec 64)
    (nonzero : words ⟨segment.val + 1, by omega⟩ ≠ BitVec.ofNat 64 0)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallStoreCall (segment.val + 1))
        (smallArguments input output word) frame
        (storageArguments output sum (smallCarryOutput segment.val sum words 1)
          (smallCarryOutput segment.val sum words 2) (smallCarryOutput segment.val sum words 3)).reverse current = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
        (smallArguments input output word) frame [.scalar (.i64 (words ⟨segment.val + 1, by omega⟩))]
        current = .ok (result, returned) ∧ post result returned := by
  unfold storageArguments at continuation
  conv at continuation in storageWordOrder => cbv
  simp [List.range_succ, List.findIdx] at continuation
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have s1 := state.slots 1
  have s2 := state.slots 2
  have s3 := state.slots 3
  dsimp at s1 s2 s3
  simp only [show (3 : Fin 4).val = 3 from rfl] at s3
  have s4 := state.sumSlot
  have r1 := load_local_word64_of_read (state.reads 1)
  have r2 := load_local_word64_of_read (state.reads 2)
  have r3 := load_local_word64_of_read (state.reads 3)
  have r4 := load_local_word64_of_read state.sumRead
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    conv in (smallIncrementDecision _) => cbv
    conv at continuation in (smallStoreCall _) => cbv
    simp [smallCarryOutput, show (3 : Fin 4).val = 3 from rfl] at continuation
    dsimp at nonzero
    repeat'
      first
      | exact continuation
      | simp (config := { failIfUnchanged := false })
        apply run_next_exists post
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, smallArguments, step, checkedValue, numericValue, formValue, formed,
              s1, s2, s3, s4, r1, r2, r3, r4, pureArity, scalars, CIL.step, CIL.truth, nonzero,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms small_carry_dispatch
#print axioms small_zero_dispatch
#print axioms SmallCarryState.nonzero_prefix

theorem SmallCarryState.overflow_prefix {original current : CIL.Safety.Memory} {frame : Frame}
    {input output sumHome : Reference} {homes : Fin 4 → Reference}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : SmallCarryState original current frame input output sumHome homes words sum)
    (word : BitVec 64) (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallStoreCall 4)
        (smallArguments input output word) frame
        (storageArguments output sum 0 0 0).reverse current = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart 3)
        (smallArguments input output word) frame [] current = .ok (result, returned) ∧ post result returned := by
  unfold storageArguments at continuation
  conv at continuation in storageWordOrder => cbv
  simp [List.range_succ, List.findIdx] at continuation
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have slot := state.sumSlot
  have reading := load_local_word64_of_read state.sumRead
  conv in (smallIncrementStart _) => cbv
  conv at continuation in (smallStoreCall _) => cbv
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, smallArguments, step, checkedValue, numericValue, formValue, formed,
            slot, reading, pureArity, scalars, CIL.step,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms SmallCarryState.overflow_prefix

end UInt256Proof.Safety
