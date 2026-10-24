import UInt256.Methods.Add.ARMBody
import CIL.Safety.ReturnArity
import UInt256.Methods.Reporting.Arithmetic
import CIL.Safety.ReturnMemory
import UInt256.Methods.Multiply.LimbStorage
import CIL.Safety.CallComposition
import UInt256.Safety.NumericStore
import CIL.Safety.StepComposition
import CIL.Safety.WordLocals
import CIL.Safety.NumericHomes

namespace UInt256Proof.Add.Safety

open CIL.Safety

def armSmallBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i32 0], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .narrow .unsigned8], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .setLocal 0,
  .arg 0,
  .fieldAt 8 8,
  .setLocal 1,
  .arg 0,
  .fieldAt 16 8,
  .setLocal 2,
  .arg 0,
  .fieldAt 24 8,
  .setLocal 3,
  .feature .advSimd,
  .brzero 55,
  .local 0,
  .arg 1,
  .add,
  .setLocal 5,
  .const32 0,
  .setLocal 6 (some .unsigned8),
  .local 5,
  .local 0,
  .bgeu 47,
  .local 1,
  .const32 1,
  .convI8,
  .add,
  .dup,
  .setLocal 1,
  .brnonzero 47,
  .local 2,
  .const32 1,
  .convI8,
  .add,
  .dup,
  .setLocal 2,
  .brnonzero 47,
  .local 3,
  .const32 1,
  .convI8,
  .add,
  .dup,
  .setLocal 3,
  .const32 0,
  .convI8,
  .eq,
  .setLocal 6 (some .unsigned8),
  .arg 2,
  .local 5,
  .local 1,
  .local 2,
  .local 3,
  .call storage 5,
  .local 6 (some .unsigned8),
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

def armSmallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

/-- Check all four input snapshots before the ARM-only arithmetic branch. -/
theorem arm_small_input_prefix (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true) (input output : Reference) (word : BitVec 64)
    (words : Fin 4 → BitVec 64) (frame : Frame) (states : Nat → Memory)
    (formed : ∀ i : Fin 4, form (states i.val) input = .ok input)
    (loads : ∀ (i : Fin 4) rest,
      instruction (.fieldAt (8*i.val) 8) (.reference (.address input) :: rest) (states i.val) =
        .ok (states i.val, .scalar (.i64 (words i)) :: rest))
    (stores : ∀ (i : Fin 4) pc rest,
      step (armSmallBody profile storage) (.setLocal i.val) pc (armSmallArguments input output word)
        frame (.scalar (.i64 (words i)) :: rest) (states i.val) =
          .ok (.next (pc + 1) rest frame (states (i.val + 1))))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method 14
        (armSmallArguments input output word) frame [] (states 4) = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run program fuel method 0
        (armSmallArguments input output word) frame [] (states 0) = .ok (result, returned) ∧
      post result returned := by
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
        · simp only [found, armSmallBody]; rfl
        · simp only [found, armSmallBody]; rfl
        · first
          | exact s0 _ _
          | exact s1 _ _
          | exact s2 _ _
          | exact s3 _ _
          | simp (config := { implicitDefEqProofs := false })
              [armSmallArguments, found, armSmallBody, step, cil_guard, observerCount, checkedValue, numericValue, formValue,
                f0, f1, f2, f3, l0, l1, l2, l3, pureArity, scalars, CIL.step.eq_def, armSmallBody, enabled, localResult,
                CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Compute the low sum from the initialized snapshot and store it in ARM local5. -/
theorem arm_small_sum (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (input output home : Reference) (word low : BitVec 64) (frame : Frame)
    (before after : Memory)
    (slot : frame.locals[0]? = some (.bytes .word64 home))
    (loaded : read before home 8 1 = .ok (numberBytes low.toNat 8))
    (stored : step (armSmallBody profile storage) (.setLocal 5) 17
      (armSmallArguments input output word) frame [.scalar (.i64 (low + word))] before =
        .ok (.next 18 [] frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method 18
        (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 14
        (armSmallArguments input output word) frame [] before = .ok (final, returned) ∧ post final returned := by
    have load := step_load_word64 (body := (armSmallBody profile storage)) (pc := 14)
      (args := armSmallArguments input output word) (stack := []) slot loaded
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact load
         | exact stored
         | (simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, armSmallArguments, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, armSmallBody, enabled, localResult, CIL.binary,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms arm_small_sum

#print axioms arm_small_input_prefix

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety

/-- Initialize the actual one-byte flag home with checked width and permission. -/
theorem arm_small_flag_zero (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (home : Reference)
    (slot : frame.locals[6]? = some (.bytes (.narrow .unsigned8) home))
    (ready : access memory home 1 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory home (numberBytes 0 1) 1 = .ok after →
      read after home 1 1 = .ok (numberBytes 0 1) →
      ∃ fuel final returned,
        run program fuel method 20 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 18 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
    obtain ⟨after, stored, written, loaded⟩ := step_store_numeric_local
      (body := (armSmallBody profile storage)) (pc := 19) (args := args) (rest := [])
      (.narrow .unsigned8) (.i32 0) 0 rfl slot ready
    have done := continuation after written loaded
    apply run_next_exists post found (by rfl)
    · simp [step, cil_guard, observerCount, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, armSmallBody, enabled, localResult,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · exact run_next_exists (op := .setLocal 6 (some .unsigned8)) post found (by rfl) stored done

/-- Compare the initialized low sum with its input snapshot and retain both actual paths: carry propagation at23 or output storage at47. -/
theorem arm_small_low_decision (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (lowHome sumHome : Reference)
    (low sum : BitVec 64)
    (lowSlot : frame.locals[0]? = some (.bytes .word64 lowHome))
    (sumSlot : frame.locals[5]? = some (.bytes .word64 sumHome))
    (lowRead : read memory lowHome 8 1 = .ok (numberBytes low.toNat 8))
    (sumRead : read memory sumHome 8 1 = .ok (numberBytes sum.toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (if sum < low then 23 else 47)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 20 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
    have loadSum := step_load_word64 (body := (armSmallBody profile storage)) (pc := 20)
      (args := args) (stack := []) sumSlot sumRead
    have loadLow := step_load_word64 (body := (armSmallBody profile storage)) (pc := 21)
      (args := args) (stack := [.scalar (.i64 sum)]) lowSlot lowRead
    apply run_next_exists post found (by rfl) loadSum
    apply run_next_exists post found (by rfl) loadLow
    by_cases carry : sum < low
    all_goals
      simp only [carry, ite_true, ite_false] at continuation
      apply run_next_exists post found (by rfl) _ continuation
      simp [step, cil_guard, observerCount, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, armSmallBody, enabled, localResult, carry,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- All three carry increments follow the same checked load/add/duplicate/store sequence. -/
theorem arm_small_increment (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (segment : Fin 3) (before after : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (word : BitVec 64)
    (slot : frame.locals[segment.val + 1]? = some (.bytes .word64 home))
    (loaded : read before home 8 1 = .ok (numberBytes word.toNat 8))
    (stored : ∀ pc rest, step (armSmallBody profile storage) (.setLocal (segment.val + 1)) pc
      args frame (.scalar (.i64 (word + 1)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (29 + 7 * segment.val)
        args frame [.scalar (.i64 (word + 1))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (23 + 7 * segment.val)
        args frame [] before = .ok (final, returned) ∧ post final returned := by
    obtain ⟨segment, bound⟩ := segment
    have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals
      dsimp at slot stored continuation ⊢
      have load := fun (pc : Nat) => step_load_word64 (body := (armSmallBody profile storage)) (pc := pc)
        (args := args) (stack := []) slot loaded
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           first
           | exact load _
           | exact stored _ _
           | (simp (config := { implicitDefEqProofs := false })
               [step, cil_guard, observerCount, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, armSmallBody, enabled, localResult, CIL.binary,
                 Bind.bind, Except.bind, Pure.pure, Except.pure]
              try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms arm_small_increment

#print axioms arm_small_flag_zero
#print axioms arm_small_low_decision
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety

/-- The first two increment results either continue propagation or join output. -/
theorem arm_small_increment_branch (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (segment : Fin 2) (memory : Memory) (frame : Frame) (args : List Value)
    (word : BitVec 64) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method
        (if word = BitVec.ofNat 64 0 then 30 + 7 * segment.val else 47)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (29 + 7 * segment.val)
        args frame [.scalar (.i64 word)] memory = .ok (final, returned) ∧ post final returned := by
    obtain ⟨segment, bound⟩ := segment
    have cases : segment = 0 ∨ segment = 1 := by omega
    rcases cases with rfl | rfl
    all_goals
      dsimp at continuation ⊢
      by_cases zero : word = BitVec.ofNat 64 0
      all_goals
        simp only [zero, ite_true, ite_false] at continuation
        apply run_next_exists post found (by rfl) _ continuation
        simp [step, cil_guard, observerCount, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.truth,
          show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, zero,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- After incrementing the top limb, equality with zero supplies the actual byte-local overflow bit. -/
theorem arm_small_final_flag (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (before after : Memory) (frame : Frame) (args : List Value) (top : BitVec 64)
    (stored : step (armSmallBody profile storage) (.setLocal 6 (some .unsigned8)) 46 args frame
      [.scalar (.i32 (if top = BitVec.ofNat 64 0 then 1 else 0))] before =
        .ok (.next 47 [] frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method 47 args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 43 args frame [.scalar (.i64 top)] before =
        .ok (final, returned) ∧ post final returned := by
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored
         | (simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.binary,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- Return the initialized byte flag as an i32 and retire the helper frame. -/
theorem arm_small_return (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (home : Reference) (flag : BitVec 32)
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (fits : localNumber (.narrow .unsigned8) (.i32 flag) = .ok flag.toNat)
    (slot : frame.locals[6]? = some (.bytes (.narrow .unsigned8) home))
    (loaded : read memory home 1 1 = .ok (numberBytes flag.toNat 1)) :
    run program 2 method 53 args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
    have load := step_load_numeric_local (body := (armSmallBody profile storage)) (pc := 53)
      (args := args) (stack := []) (.narrow .unsigned8) (.i32 flag) flag.toNat fits slot loaded
    apply Eq.trans (run_next (op := .local 6 (some .unsigned8)) found (by rfl) load)
    have fetched : (armSmallBody profile storage).code[54]? = some (.ret (some .unsigned8)) := by rfl
    have returns : (armSmallBody profile storage).returnsValue = true := by rfl
    simp [run, found, fetched, returns, step, cil_guard, observerCount, checkedValue, numericValue, localResult, flagFit, List.mapM, Option.bind,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

/-- Prepare StoreLimbs from saved private values, never rereading caller inputs. -/
theorem arm_small_output_arguments (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (output : Reference)
    (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (slots : ∀ i : Fin 4, frame.locals[if i.val = 0 then 5 else i.val]? =
      some (.bytes .word64 (homes i)))
    (reads : ∀ i : Fin 4, read memory (homes i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (argument : args[2]? = some (.reference (.address output)))
    (formed : form memory output = .ok output)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method 52 args frame
        [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory =
            .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 47 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
    have loads := fun (i : Fin 4) (pc : Nat) (stack : List Value) => step_load_word64
      (body := (armSmallBody profile storage)) (pc := pc) (args := args) (stack := stack) (slots i) (reads i)
    have l0 := loads 0
    have l1 := loads 1
    have l2 := loads 2
    have l3 := loads 3
    dsimp at l0 l1 l2 l3
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact l0 _ _
         | exact l1 _ _
         | exact l2 _ _
         | exact l3 _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, argument, checkedValue, formValue, formed,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms arm_small_output_arguments

#print axioms arm_small_increment_branch
#print axioms arm_small_final_flag
#print axioms arm_small_return
end UInt256Proof.Add.Safety
