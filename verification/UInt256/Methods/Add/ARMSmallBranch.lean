import Extracted
import CIL.Safety.StepComposition
import CIL.Safety.WordLocals
import CIL.Safety.NumericHomes

namespace UInt256Proof.Add.Safety

open CIL.Safety

def armSmallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

/-- Check all four input snapshots before the ARM-only arithmetic branch.
    Every load/store premise is an actual checked operation, not a helper summary. -/
theorem arm_small_input_prefix (enabled : Extracted.profile.advSimd = true) (input output : Reference) (word : BitVec 64)
    (words : Fin 4 → BitVec 64) (frame : Frame) (states : Nat → Memory)
    (formed : ∀ i : Fin 4, form (states i.val) input = .ok input)
    (loads : ∀ (i : Fin 4) rest,
      instruction (.field i) (.reference (.address input) :: rest) (states i.val) =
        .ok (states i.val, .scalar (.i64 (words i)) :: rest))
    (stores : ∀ (i : Fin 4) pc rest,
      step Extracted.addScalarUInt64Body (.setLocal i.val) pc (armSmallArguments input output word)
        frame (.scalar (.i64 (words i)) :: rest) (states i.val) =
          .ok (.next (pc + 1) rest frame (states (i.val + 1))))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 14
        (armSmallArguments input output word) frame [] (states 4) = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (armSmallArguments input output word) frame [] (states 0) = .ok (result, returned) ∧
      post result returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
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
              [armSmallArguments, cil_code, step, checkedValue, numericValue, formValue,
                f0, f1, f2, f3, l0, l1, l2, l3, pureArity, scalars, CIL.step,
                CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩


/-- Compute the low sum from the initialized snapshot and store it in ARM local5. -/
theorem arm_small_sum (enabled : Extracted.profile.advSimd = true)
    (input output home : Reference) (word low : BitVec 64) (frame : Frame)
    (before after : Memory)
    (slot : frame.locals[0]? = some (.bytes .word64 home))
    (loaded : read before home 8 1 = .ok (numberBytes low.toNat 8))
    (stored : step Extracted.addScalarUInt64Body (.setLocal 5) 17
      (armSmallArguments input output word) frame [.scalar (.i64 (low + word))] before =
        .ok (.next 18 [] frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 18
        (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 14
        (armSmallArguments input output word) frame [] before = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    have load := step_load_word64 (body := Extracted.addScalarUInt64Body) (pc := 14)
      (args := armSmallArguments input output word) (stack := []) slot loaded
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact load
         | exact stored
         | (simp (config := { implicitDefEqProofs := false })
             [step, armSmallArguments, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms arm_small_sum

#print axioms arm_small_input_prefix

end UInt256Proof.Add.Safety

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
