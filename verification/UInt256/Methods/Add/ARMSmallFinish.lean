import UInt256.Methods.Add.ARMSmallBranch

namespace UInt256Proof.Add.Safety
open CIL.Safety

/-- The first two increment results either continue propagation or join output. -/
theorem arm_small_increment_branch (enabled : Extracted.profile.advSimd = true)
    (segment : Fin 2) (memory : Memory) (frame : Frame) (args : List Value)
    (word : BitVec 64) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index
        (if word = BitVec.ofNat 64 0 then 30 + 7 * segment.val else 47)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (29 + 7 * segment.val)
        args frame [.scalar (.i64 word)] memory = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    obtain ⟨segment, bound⟩ := segment
    have cases : segment = 0 ∨ segment = 1 := by omega
    rcases cases with rfl | rfl
    all_goals
      dsimp at continuation ⊢
      by_cases zero : word = BitVec.ofNat 64 0
      all_goals
        simp only [zero, ite_true, ite_false] at continuation
        apply run_next_exists post found (by rfl) _ continuation
        simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.truth,
          show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, zero,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- After incrementing the top limb, equality with zero supplies the actual
    byte-local overflow bit. Its arithmetic interpretation is proved separately. -/
theorem arm_small_final_flag (enabled : Extracted.profile.advSimd = true)
    (before after : Memory) (frame : Frame) (args : List Value) (top : BitVec 64)
    (stored : step Extracted.addScalarUInt64Body (.setLocal 6) 46 args frame
      [.scalar (.i32 (if top = BitVec.ofNat 64 0 then 1 else 0))] before =
        .ok (.next 47 [] frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 47 args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 43 args frame [.scalar (.i64 top)] before =
        .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored
         | (simp (config := { implicitDefEqProofs := false })
             [step, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Return the initialized byte flag as an i32 and retire the helper frame. -/
theorem arm_small_return (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (home : Reference) (flag : BitVec 32)
    (fits : localNumber .byte (.i32 flag) = .ok flag.toNat)
    (slot : frame.locals[6]? = some (.bytes .byte home))
    (loaded : read memory home 1 1 = .ok (numberBytes flag.toNat 1)) :
    run Extracted.program 2 Extracted.addScalarUInt64Index 53 args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    have load := step_load_numeric_local (body := Extracted.addScalarUInt64Body) (pc := 53)
      (args := args) (stack := []) .byte (.i32 flag) flag.toNat fits slot loaded
    apply Eq.trans (run_next found (by rfl) load)
    have fetched : Extracted.addScalarUInt64Body.code[54]? = some .ret := by rfl
    have returns : Extracted.addScalarUInt64Body.returnsValue = true := by rfl
    simp [run, found, fetched, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]


/-- Prepare StoreLimbs from saved private values, never rereading caller inputs. -/
theorem arm_small_output_arguments (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (output : Reference)
    (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (slots : ∀ i : Fin 4, frame.locals[if i.val = 0 then 5 else i.val]? =
      some (.bytes .word64 (homes i)))
    (reads : ∀ i : Fin 4, read memory (homes i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (argument : args[2]? = some (.reference (.address output)))
    (formed : form memory output = .ok output)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 52 args frame
        [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory =
            .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 47 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarUInt64Index]? = some Extracted.addScalarUInt64Body := by rfl
    have loads := fun (i : Fin 4) (pc : Nat) (stack : List Value) => step_load_word64
      (body := Extracted.addScalarUInt64Body) (pc := pc) (args := args) (stack := stack) (slots i) (reads i)
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
             [step, argument, checkedValue, formValue, formed,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms arm_small_output_arguments

#print axioms arm_small_increment_branch
#print axioms arm_small_final_flag
#print axioms arm_small_return
end UInt256Proof.Add.Safety
