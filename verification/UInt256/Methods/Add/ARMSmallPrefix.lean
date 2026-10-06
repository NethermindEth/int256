import Extracted
import CIL.Safety.StepComposition
import CIL.Safety.WordLocals

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
