import UInt256.Methods.Add.ARMSmallPrefix
import CIL.Safety.NumericHomes

namespace UInt256Proof.Add.Safety
open CIL.Safety

/-- Initialize the actual one-byte flag home with checked width and permission. -/
theorem arm_small_flag_zero (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (home : Reference)
    (slot : frame.locals[6]? = some (.bytes .byte home))
    (ready : access memory home 1 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory home (numberBytes 0 1) 1 = .ok after →
      read after home 1 1 = .ok (numberBytes 0 1) →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 20 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 18 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨after, stored, written, loaded⟩ := step_store_numeric_local
      (body := Extracted.addScalarUInt64Body) (pc := 19) (args := args) (rest := [])
      .byte (.i32 0) 0 rfl slot ready
    have done := continuation after written loaded
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    apply run_next_exists post found (by rfl)
    · simp [step, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · exact run_next_exists post found (by rfl) stored done

/-- Compare the initialized low sum with its input snapshot and retain both
    actual paths: carry propagation at23 or output storage at47. -/
theorem arm_small_low_decision (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (lowHome sumHome : Reference)
    (low sum : BitVec 64)
    (lowSlot : frame.locals[0]? = some (.bytes .word64 lowHome))
    (sumSlot : frame.locals[5]? = some (.bytes .word64 sumHome))
    (lowRead : read memory lowHome 8 1 = .ok (numberBytes low.toNat 8))
    (sumRead : read memory sumHome 8 1 = .ok (numberBytes sum.toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (if sum < low then 23 else 47)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 20 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    have loadSum := step_load_word64 (body := Extracted.addScalarUInt64Body) (pc := 20)
      (args := args) (stack := []) sumSlot sumRead
    have loadLow := step_load_word64 (body := Extracted.addScalarUInt64Body) (pc := 21)
      (args := args) (stack := [.scalar (.i64 sum)]) lowSlot lowRead
    apply run_next_exists post found (by rfl) loadSum
    apply run_next_exists post found (by rfl) loadLow
    by_cases carry : sum < low
    all_goals
      simp only [carry, ite_true, ite_false] at continuation
      apply run_next_exists post found (by rfl) _ continuation
      simp [step, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step, carry,
        Bind.bind, Except.bind, Pure.pure, Except.pure]


/-- All three carry increments follow the same checked load/add/duplicate/store
    sequence. The final limb keeps its value for the separate overflow-flag test. -/
theorem arm_small_increment (enabled : Extracted.profile.advSimd = true)
    (segment : Fin 3) (before after : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (word : BitVec 64)
    (slot : frame.locals[segment.val + 1]? = some (.bytes .word64 home))
    (loaded : read before home 8 1 = .ok (numberBytes word.toNat 8))
    (stored : ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal (segment.val + 1)) pc
      args frame (.scalar (.i64 (word + 1)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (29 + 7 * segment.val)
        args frame [.scalar (.i64 (word + 1))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (23 + 7 * segment.val)
        args frame [] before = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    obtain ⟨segment, bound⟩ := segment
    have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals
      dsimp at slot stored continuation ⊢
      have load := fun (pc : Nat) => step_load_word64 (body := Extracted.addScalarUInt64Body) (pc := pc)
        (args := args) (stack := []) slot loaded
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           first
           | exact load _
           | exact stored _ _
           | (simp (config := { implicitDefEqProofs := false })
               [step, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
                 Bind.bind, Except.bind, Pure.pure, Except.pure]
              first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms arm_small_increment

#print axioms arm_small_flag_zero
#print axioms arm_small_low_decision
end UInt256Proof.Add.Safety
