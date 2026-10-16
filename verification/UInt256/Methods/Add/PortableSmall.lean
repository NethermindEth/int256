import UInt256.Methods.Add.ARMSmallContract

namespace UInt256Proof.Add.Safety

open CIL.Safety

-- AddScalarUInt64 with the AdvSimd branch disabled: one store and constant flag per carry exit.
def portableSmallBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i32 0], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .narrow .unsigned8], parameterHomes := [], staticSites := [], code := [
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
  .local 0,
  .arg 1,
  .add,
  .setLocal 4,
  .local 4,
  .local 0,
  .bltu 70,
  .arg 2,
  .local 4,
  .local 1,
  .local 2,
  .local 3,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .local 1,
  .const32 1,
  .convI8,
  .add,
  .dup,
  .setLocal 1,
  .brzero 85,
  .arg 2,
  .local 4,
  .local 1,
  .local 2,
  .local 3,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .local 2,
  .const32 1,
  .convI8,
  .add,
  .dup,
  .setLocal 2,
  .brzero 101,
  .arg 2,
  .local 4,
  .const32 0,
  .convI8,
  .local 2,
  .local 3,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .local 3,
  .const32 1,
  .convI8,
  .add,
  .dup,
  .setLocal 3,
  .brzero 118,
  .arg 2,
  .local 4,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .local 3,
  .call storage 5,
  .const32 0,
  .ret (some .unsigned8),
  .arg 2,
  .local 4,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .call storage 5,
  .const32 1,
  .ret (some .unsigned8)] }

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem portable_small_frame_setup (profile : CIL.FeatureProfile) (storage : Nat) (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame (portableSmallBody profile storage) args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity armSmallSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup (portableSmallBody profile storage) armSmallSpecs (by rfl) (by rfl) (by rfl) (by rfl) memory args wf

theorem portable_small_private_store (program : CIL.Program) (profile : CIL.FeatureProfile) (storage : Nat) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame)
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary armSmallSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec) (specified : armSmallSpecs[index]? = some spec)
    (value : CIL.Value) (number : Nat) (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 = .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step (portableSmallBody profile storage) (.setLocal index) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) :=
  checked_numeric_store program (portableSmallBody profile storage) armSmallSpecs boundary
    entered current inputs outputs frame call enteredWF homes authority index spec specified value number fits

/-- Check all four input snapshots, then take the disabled AdvSimd branch to the scalar sum. -/
theorem portable_small_input_prefix (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage)) (disabled : profile.advSimd = false) (input output : Reference) (word : BitVec 64)
    (words : Fin 4 → BitVec 64) (frame : Frame) (states : Nat → Memory)
    (formed : ∀ i : Fin 4, form (states i.val) input = .ok input)
    (loads : ∀ (i : Fin 4) rest,
      instruction (.fieldAt (8*i.val) 8) (.reference (.address input) :: rest) (states i.val) =
        .ok (states i.val, .scalar (.i64 (words i)) :: rest))
    (stores : ∀ (i : Fin 4) pc rest,
      step (portableSmallBody profile storage) (.setLocal i.val) pc (armSmallArguments input output word)
        frame (.scalar (.i64 (words i)) :: rest) (states i.val) =
          .ok (.next (pc + 1) rest frame (states (i.val + 1))))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method 55
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
        · simp only [found, portableSmallBody]; rfl
        · simp only [found, portableSmallBody]; rfl
        · first
          | exact s0 _ _
          | exact s1 _ _
          | exact s2 _ _
          | exact s3 _ _
          | simp (config := { implicitDefEqProofs := false })
              [armSmallArguments, found, step, checkedValue, numericValue, formValue,
                f0, f1, f2, f3, l0, l1, l2, l3, pureArity, scalars, CIL.step.eq_def, disabled, localResult,
                CIL.FeatureProfile.evaluate, CIL.truth, checkedAt, Except.mapError,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem portable_small_save {program : CIL.Program} {profile : CIL.FeatureProfile} {storage : Nat} {original entered current : Memory}
    {input output : Reference} {frame : Frame}
    (index : Fin 4) (state : ARMSmallSaved program original entered current input output frame index.val)
    (word : BitVec 64) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after, ARMSmallSaved program original entered after input output frame (index.val + 1) ∧
      ∀ pc rest, step (portableSmallBody profile storage) (.setLocal index.val) pc
        (armSmallArguments input output word) frame
        (.scalar (.i64 (inputLimb original input index)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, authority, written, stepped⟩ :=
    portable_small_private_store program profile storage original.nextIdentity entered current [input] [output] frame
      state.call enteredWF homes state.authority index.val armSmallWordSpec (arm_small_input_spec index)
      (.i64 (inputLimb original input index)) (inputLimb original input index).toNat rfl
  refine ⟨after, ⟨afterCall, state.preserved.trans preserved, authority, ?_⟩,
    fun pc rest => stepped pc _ rest⟩
  intro i saved
  by_cases equal : i = index
  · subst i
    exact ⟨reference, slot, loaded⟩
  · have earlier : i.val < index.val := by
      have different : i.val ≠ index.val := fun h => equal (Fin.ext h)
      omega
    obtain ⟨previous, previousSlot, previousRead⟩ := state.completed i earlier
    have different := Nat.ne_of_lt
      (homes.ordered i.val index.val .word64 .word64 previous reference earlier previousSlot slot)
    exact ⟨previous, previousSlot,
      write_preserves_disjoint_read written previousRead (Or.inl different)⟩

theorem portable_small_input_prefix_checked (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage)) (disabled : profile.advSimd = false) (original entered : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (portableSmallBody profile storage) (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after, ARMSmallSaved program original entered after input output frame 4 →
      ∃ fuel result returned,
        run program fuel method 55
          (armSmallArguments input output word) frame [] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method 0
        (armSmallArguments input output word) frame [] entered = .ok (result, returned) ∧
      post result returned := by
  have enteredCall := call.after_frame_setup setup
  have initial : ARMSmallSaved program original entered entered input output frame 0 :=
    ⟨enteredCall, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow, by intro i impossible; omega⟩
  obtain ⟨first, saved1, step0⟩ := portable_small_save (profile := profile) (storage := storage) 0 initial word enteredCall.1.1 homes
  obtain ⟨second, saved2, step1⟩ := portable_small_save (profile := profile) (storage := storage) 1 saved1 word enteredCall.1.1 homes
  obtain ⟨third, saved3, step2⟩ := portable_small_save (profile := profile) (storage := storage) 2 saved2 word enteredCall.1.1 homes
  obtain ⟨fourth, saved4, step3⟩ := portable_small_save (profile := profile) (storage := storage) 3 saved3 word enteredCall.1.1 homes
  let states : Nat → CIL.Safety.Memory := fun n => match n with
    | 0 => entered | 1 => first | 2 => second | 3 => third | _ => fourth
  have saved : ∀ i : Fin 4, ARMSmallSaved program original entered (states i.val) input output frame i.val := by
    intro ⟨i, bound⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact initial
    · exact saved1
    · exact saved2
    · exact saved3
  apply portable_small_input_prefix program method storage profile found disabled input output word (inputLimb original input) frame states
    (fun i => (saved i).call.input_formed (by simp)) ?_ ?_ post
    (continuation fourth saved4)
  · intro i rest
    rw [(saved i).call.input_field_instruction (by simp) i rest]
    simp only [inputLimb,
      call.input_bytes_of_memory_below (saved i).preserved (reference := input) (by simp)]
  · intro ⟨i, bound⟩ pc rest
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact step0 pc rest
    · exact step1 pc rest
    · exact step2 pc rest
    · exact step3 pc rest

#print axioms portable_small_frame_setup
#print axioms portable_small_private_store
#print axioms portable_small_input_prefix
#print axioms portable_small_save
#print axioms portable_small_input_prefix_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

structure PortableSmallState (program : CIL.Program) (original entered current : Memory) (input output : Reference)
    (frame : Frame) (words : Fin 4 → BitVec 64) (sum : BitVec 64) : Prop where
  call : CallingConditions program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  limbs : ∀ i : Fin 4, ∃ home, frame.locals[i.val]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes (words i).toNat 8)
  sumRead : ∃ home, frame.locals[4]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes sum.toNat 8)

/-- Store the low sum in local4 without disturbing the four saved input limbs. -/
theorem portable_small_prepare (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage))
    (original entered current : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (saved : ARMSmallSaved program original entered current input output frame 4)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, PortableSmallState program original entered after input output frame
      (inputLimb original input) (inputLimb original input 0 + word) →
      ∃ fuel final returned,
        run program fuel method 59
          (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 55
        (armSmallArguments input output word) frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨lowHome, lowSlot, lowRead⟩ := saved.completed 0 (by decide)
  obtain ⟨sumHome, after, sumSlot, sumRead, sumPreserved, _, _, sumWritten, sumStep⟩ :=
    portable_small_private_store program profile storage original.nextIdentity entered current [input] [output] frame
      saved.call enteredWF homes saved.authority 4 armSmallWordSpec (by rfl)
      (.i64 (inputLimb original input 0 + word)) (inputLimb original input 0 + word).toNat rfl
  have afterSaved := saved.after_later_write homes (by decide : 4 ≤ 4) sumSlot sumWritten sumPreserved
  have state : PortableSmallState program original entered after input output frame
      (inputLimb original input) (inputLimb original input 0 + word) :=
    ⟨afterSaved.call, afterSaved.preserved, afterSaved.authority,
      fun i => afterSaved.completed i i.isLt, ⟨sumHome, sumSlot, sumRead⟩⟩
  have load := step_load_word64 (body := portableSmallBody profile storage) (pc := 55)
    (args := armSmallArguments input output word) (stack := []) lowSlot lowRead
  have stored := sumStep 58 (armSmallArguments input output word) []
  have done := continuation after state
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact load
       | exact stored
       | (simp (config := { implicitDefEqProofs := false })
           [step, armSmallArguments, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, localResult, CIL.binary,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- Compare the stored low sum with the saved low limb: carry at70, no-carry output at62. -/
theorem portable_small_low_decision (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage))
    (memory : Memory) (frame : Frame) (args : List Value) (lowHome sumHome : Reference)
    (low sum : BitVec 64)
    (lowSlot : frame.locals[0]? = some (.bytes .word64 lowHome))
    (sumSlot : frame.locals[4]? = some (.bytes .word64 sumHome))
    (lowRead : read memory lowHome 8 1 = .ok (numberBytes low.toNat 8))
    (sumRead : read memory sumHome 8 1 = .ok (numberBytes sum.toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (if sum < low then 70 else 62)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 59 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have loadSum := step_load_word64 (body := portableSmallBody profile storage) (pc := 59)
    (args := args) (stack := []) sumSlot sumRead
  have loadLow := step_load_word64 (body := portableSmallBody profile storage) (pc := 60)
    (args := args) (stack := [.scalar (.i64 sum)]) lowSlot lowRead
  apply run_next_exists post found (by rfl) loadSum
  apply run_next_exists post found (by rfl) loadLow
  by_cases carry : sum < low
  all_goals
    simp only [carry, ite_true, ite_false] at continuation
    apply run_next_exists post found (by rfl) _ continuation
    simp [step, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, localResult, carry,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

def portableIncrementStart : Fin 3 → Nat
  | 0 => 70 | 1 => 85 | 2 => 101

def portableIncrementZero : Fin 3 → Nat
  | 0 => 85 | 1 => 101 | 2 => 118

/-- One carry increment: store the incremented limb and continue only while it wrapped to zero. -/
theorem portable_small_increment (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage))
    (segment : Fin 3) (before after : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (word : BitVec 64)
    (slot : frame.locals[segment.val + 1]? = some (.bytes .word64 home))
    (loaded : read before home 8 1 = .ok (numberBytes word.toNat 8))
    (stored : ∀ pc rest, step (portableSmallBody profile storage) (.setLocal (segment.val + 1)) pc
      args frame (.scalar (.i64 (word + 1)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method
        (if word + 1 = BitVec.ofNat 64 0 then portableIncrementZero segment else portableIncrementStart segment + 7)
        args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (portableIncrementStart segment)
        args frame [] before = .ok (final, returned) ∧ post final returned := by
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  have load := fun (pc : Nat) => step_load_word64 (body := portableSmallBody profile storage) (pc := pc)
    (args := args) (stack := []) slot loaded
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp only [portableIncrementStart, portableIncrementZero, Nat.reduceAdd] at slot stored continuation load ⊢
    by_cases zero : word + 1 = BitVec.ofNat 64 0
    all_goals
      simp only [zero, ite_true, ite_false] at continuation
      have zero' := zero
      try simp only [BitVec.ofNat_eq_ofNat] at zero'
      iterate 6
        apply run_next_exists post found (by rfl)
        first
        | exact load _
        | exact stored _ _
        | (simp (config := { implicitDefEqProofs := false })
            [step, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, localResult, CIL.binary,
              CIL.unary, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
      apply run_next_exists post found (by rfl) _ continuation
      simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth,
        BitVec.ofNat_eq_ofNat, zero', Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms portable_small_prepare
#print axioms portable_small_low_decision
#print axioms portable_small_increment
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem PortableSmallState.store_limb {program : CIL.Program} {profile : CIL.FeatureProfile} {storage : Nat} {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : PortableSmallState program original entered current input output frame words sum)
    (index : Fin 4) (value : BitVec 64) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after,
      PortableSmallState program original entered after input output frame
        (fun i => if i = index then value else words i) sum ∧
      ∀ pc args rest, step (portableSmallBody profile storage) (.setLocal index.val) pc args frame
        (.scalar (.i64 value) :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨home, after, slot, loaded, preserved, call, authority, written, stepped⟩ :=
    portable_small_private_store program profile storage original.nextIdentity entered current [input] [output] frame
      state.call enteredWF homes state.authority index.val armSmallWordSpec (arm_small_input_spec index)
      (.i64 value) value.toNat rfl
  refine ⟨after, ⟨call, state.preserved.trans preserved, authority, ?_, ?_⟩, stepped⟩
  · intro i
    by_cases same : i = index
    · subst i
      exact ⟨home, slot, by simpa [armSmallWordSpec, localWidth] using loaded⟩
    · obtain ⟨other, otherSlot, otherRead⟩ := state.limbs i
      refine ⟨other, otherSlot, ?_⟩
      simp only [same, ite_false]
      exact arm_small_other_read homes (fun h => same (Fin.ext h)) otherSlot slot written otherRead
  · obtain ⟨other, otherSlot, otherRead⟩ := state.sumRead
    exact ⟨other, otherSlot, arm_small_other_read homes (by omega) otherSlot slot written otherRead⟩

/-- Execute one carry increment with every memory premise derived from the state. -/
theorem PortableSmallState.increment (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage))
    {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : PortableSmallState program original entered current input output frame words sum)
    (segment : Fin 3) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PortableSmallState program original entered after input output frame
        (armIncrementWord words ⟨segment.val + 1, by omega⟩) sum →
      ∃ fuel final returned,
        run program fuel method
          (if words ⟨segment.val + 1, by omega⟩ + 1 = BitVec.ofNat 64 0
            then portableIncrementZero segment else portableIncrementStart segment + 7)
          args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (portableIncrementStart segment) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  obtain ⟨home, slot, loaded⟩ := state.limbs index
  obtain ⟨after, updated, stored⟩ := state.store_limb (profile := profile) (storage := storage) index (words index + 1) enteredWF homes
  exact portable_small_increment program method storage profile found segment current after frame args home (words index) slot loaded
    (fun pc rest => stored pc args rest) post (continuation after updated)

/-- Store four words through StoreLimbs, then return the constant flag. -/
theorem portable_small_store_return (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (memory : Memory) (frame : Frame) (args : List Value) (inputs : List Reference)
    (output : Reference) (words : Fin 4 → BitVec 64) (flag : BitVec 32) (callPc : Nat)
    (callAt : (portableSmallBody profile storage).code[callPc]? = some (.call storage 5))
    (constAt : (portableSmallBody profile storage).code[callPc + 1]? = some (.const32 flag))
    (retAt : (portableSmallBody profile storage).code[callPc + 1 + 1]? = some (.ret (some .unsigned8)))
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory inputs [output])
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored,
      CallingConditions program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = memory.cells id offset) →
      AccessBelow memory.nextIdentity memory stored →
      inputValue stored output = UInt256Model.value words →
      post (leaveFrame frame stored) [.scalar (.i32 flag)]) :
    ∃ fuel final returned,
      run program fuel method callPc args frame
        [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory =
            .ok (final, returned) ∧ post final returned := by
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, readable⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract profile program storage storageFound
      memory inputs output (words 0) (words 1) (words 2) (words 3) call
  have formed := call.output_formed (by simp : output ∈ [output])
  have stepped : step (portableSmallBody profile storage) (.call storage 5) callPc args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] memory =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3)) [] memory) := by
    simp [step, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  have returned : run program 2 method (callPc + 1) args frame [] stored =
      .ok (leaveFrame frame stored, [.scalar (.i32 flag)]) := by
    have constStep : step (portableSmallBody profile storage) (.const32 flag) (callPc + 1) args frame [] stored =
        .ok (.next (callPc + 1 + 1) [.scalar (.i32 flag)] frame stored) := by
      simp [step, instruction, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [run_next found constAt constStep]
    have returns : (portableSmallBody profile storage).returnsValue = true := by rfl
    simp [run, found, retAt, returns, step, checkedValue, numericValue, flagFit, List.mapM, List.mapM.loop, Option.bind,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, executed⟩ := run_call_exists found callAt stepped ⟨childFuel, invoked⟩ ⟨2, returned⟩
  refine ⟨fuel, leaveFrame frame stored, [.scalar (.i32 flag)], executed, ?_⟩
  apply continuation stored valid outside authority
  simpa only [UInt256Model.value] using value

#print axioms PortableSmallState.store_limb
#print axioms PortableSmallState.increment
#print axioms portable_small_store_return
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def portableSiteStart : Fin 5 → Nat
  | 0 => 62 | 1 => 77 | 2 => 92 | 3 => 108 | 4 => 118

def portableSiteCall : Fin 5 → Nat
  | 0 => 67 | 1 => 82 | 2 => 98 | 3 => 115 | 4 => 126

def portableSiteZeros : Fin 5 → Nat
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3

def portableSiteFlag (site : Fin 5) : BitVec 32 := if site.val = 4 then 1 else 0

/-- Words stored at an exit: the low sum, then constant zeros for wrapped limbs, then saved limbs. -/
def portableSiteWords (site : Fin 5) (words : Fin 4 → BitVec 64) (sum : BitVec 64) : Fin 4 → BitVec 64 :=
  fun i => if i.val = 0 then sum else if i.val ≤ portableSiteZeros site then 0 else words i

/-- Every exit loads its output words from the state and returns its constant flag. -/
theorem PortableSmallState.finish (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    {original entered current : Memory} {input output : Reference} {frame : Frame}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : PortableSmallState program original entered current input output frame words sum)
    (site : Fin 5) (args : List Value) (argument : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored,
      CallingConditions program stored [input] [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = current.cells id offset) →
      AccessBelow current.nextIdentity current stored →
      inputValue stored output = UInt256Model.value (portableSiteWords site words sum) →
      post (leaveFrame frame stored) [.scalar (.i32 (portableSiteFlag site))]) :
    ∃ fuel final returned,
      run program fuel method (portableSiteStart site) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨h1, s1, r1⟩ := state.limbs 1
  obtain ⟨h2, s2, r2⟩ := state.limbs 2
  obtain ⟨h3, s3, r3⟩ := state.limbs 3
  obtain ⟨h4, s4, r4⟩ := state.sumRead
  have l1 := fun pc stack => step_load_word64 (body := portableSmallBody profile storage) (pc := pc) (args := args) (stack := stack) s1 r1
  have l2 := fun pc stack => step_load_word64 (body := portableSmallBody profile storage) (pc := pc) (args := args) (stack := stack) s2 r2
  have l3 := fun pc stack => step_load_word64 (body := portableSmallBody profile storage) (pc := pc) (args := args) (stack := stack) s3 r3
  have l4 := fun pc stack => step_load_word64 (body := portableSmallBody profile storage) (pc := pc) (args := args) (stack := stack) s4 r4
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have finishing := fun (callPc : Nat) callAt constAt retAt flagFit =>
    portable_small_store_return program method storage profile found storageFound current frame args [input] output
      (portableSiteWords site words sum) (portableSiteFlag site) callPc callAt constAt retAt flagFit state.call post continuation
  obtain ⟨site, bound⟩ := site
  have cases : site = 0 ∨ site = 1 ∨ site = 2 ∨ site = 3 ∨ site = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals
    have done := finishing (portableSiteCall ⟨_, bound⟩) (by rfl) (by rfl) (by rfl) (by rfl)
    simp only [portableSiteWords, portableSiteZeros, portableSiteCall, portableSiteStart] at done ⊢
    try dsimp only [Fin.isValue] at done
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact l1 _ _
         | exact l2 _ _
         | exact l3 _ _
         | exact l4 _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, instruction, argument, checkedValue, formValue, formed, numericValue, pureArity, scalars,
               CIL.step.eq_def, CIL.unary, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms PortableSmallState.finish
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Each exit's stored words and constant flag agree with the shared small-sum result. -/
def PortableSiteAgrees (site : Fin 5) (current : Fin 4 → BitVec 64) (words : Fin 4 → BitVec 64) (word : BitVec 64) : Prop :=
  portableSiteWords site current (words 0 + word) = armSmallOutputWords (armSmallResult words word).1 (words 0 + word) ∧
  portableSiteFlag site = (armSmallResult words word).2

theorem portable_site_no_carry (words : Fin 4 → BitVec 64) (word : BitVec 64) (carry : ¬ words 0 + word < words 0) :
    PortableSiteAgrees 0 words words word := by
  constructor
  · funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [portableSiteWords, portableSiteZeros, armSmallOutputWords, armSmallResult, carry]
  · simp [portableSiteFlag, armSmallResult, carry]

theorem portable_site_first (words : Fin 4 → BitVec 64) (word : BitVec 64) (carry : words 0 + word < words 0)
    (first : ¬ words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) :
    PortableSiteAgrees 1 (armIncrementWord words 1) words word := by
  constructor
  · funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [portableSiteWords, portableSiteZeros, armSmallOutputWords, armSmallResult, armCarryResult, armIncrementWord, carry, first]
  · simp [portableSiteFlag, armSmallResult, armCarryResult, armIncrementWord, carry, first]

theorem portable_site_second (words : Fin 4 → BitVec 64) (word : BitVec 64) (carry : words 0 + word < words 0)
    (first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) (second : ¬ words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) :
    PortableSiteAgrees 2 (armIncrementWord (armIncrementWord words 1) 2) words word := by
  constructor
  · funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [portableSiteWords, portableSiteZeros, armSmallOutputWords, armSmallResult, armCarryResult, armIncrementWord, carry, first, second]
  · simp [portableSiteFlag, armSmallResult, armCarryResult, armIncrementWord, carry, first, second]

theorem portable_site_third (words : Fin 4 → BitVec 64) (word : BitVec 64) (carry : words 0 + word < words 0)
    (first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) (second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) (third : ¬ words 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) :
    PortableSiteAgrees 3 (armIncrementWord (armIncrementWord (armIncrementWord words 1) 2) 3) words word := by
  constructor
  · funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [portableSiteWords, portableSiteZeros, armSmallOutputWords, armSmallResult, armCarryResult, armIncrementWord, carry, first, second, third]
  · simp [portableSiteFlag, armSmallResult, armCarryResult, armIncrementWord, carry, first, second, third]
    all_goals decide

theorem portable_site_overflow (words : Fin 4 → BitVec 64) (word : BitVec 64) (carry : words 0 + word < words 0)
    (first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) (second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) (third : words 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0) :
    PortableSiteAgrees 4 (armIncrementWord (armIncrementWord (armIncrementWord words 1) 2) 3) words word := by
  constructor
  · funext ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [portableSiteWords, portableSiteZeros, armSmallOutputWords, armSmallResult, armCarryResult, armIncrementWord, carry, first, second, third]
  · simp [portableSiteFlag, armSmallResult, armCarryResult, armIncrementWord, carry, first, second, third]
    all_goals decide

#print axioms portable_site_no_carry
#print axioms portable_site_first
#print axioms portable_site_second
#print axioms portable_site_third
#print axioms portable_site_overflow
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- An exit whose words agree with the small-sum result establishes the helper postcondition. -/
theorem PortableSmallState.exit (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    {original entered current : Memory} {input output : Reference} {word : BitVec 64} {frame : Frame}
    {words : Fin 4 → BitVec 64}
    (state : PortableSmallState program original entered current input output frame words (inputLimb original input 0 + word))
    (site : Fin 5) (agrees : PortableSiteAgrees site words (inputLimb original input) word)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (portableSmallBody profile storage) (armSmallArguments input output word) original =
      .ok (frame, entered)) :
    ∃ fuel final returned,
      run program fuel method (portableSiteStart site)
        (armSmallArguments input output word) frame [] current = .ok (final, returned) ∧
      ARMSmallPost original final returned input output word := by
  apply state.finish program method storage profile found storageFound site (armSmallArguments input output word) (by rfl)
    (fun final returned => ARMSmallPost original final returned input output word)
  intro stored valid outside _ value
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retired := leaveFrame_preserves_memory_below frame stored original.nextIdentity
    (fun id member => (fresh.2 id member).1)
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retired.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have mathematical := (value.trans (congrArg UInt256Model.value agrees.1)).trans
      (arm_small_result_value original input word)
    simpa only [inputValue, bytes] using mathematical
  · have initial : UInt256Model.value (inputLimb original input) = inputValue original input :=
      UInt256Proof.input_value (fun offset => (original.cells input.allocation offset).bits) input.offset
    have exactFlag := arm_small_result_flag (inputLimb original input) word
    rw [initial] at exactFlag
    rw [agrees.2, exactFlag]
  · exact (retired.access output outputOld 32 1 true).trans
      (valid.1.2.2 (wordView output) (by simp))
  · intro id old offset untouched
    exact (retired.cells id old offset).trans
      ((outside id offset untouched).trans (state.preserved.cells id old offset))

/-- Full portable helper execution: input snapshots, low sum, every carry exit, and the shared postcondition. -/
theorem portable_small_entry (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage)) (disabled : profile.advSimd = false)
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (portableSmallBody profile storage) (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ fuel final returned,
      run program fuel method 0
        (armSmallArguments input output word) frame [] entered = .ok (final, returned) ∧
      ARMSmallPost original final returned input output word := by
  let post := fun final returned => ARMSmallPost original final returned input output word
  let args := armSmallArguments input output word
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply portable_small_input_prefix_checked program method storage profile found disabled original entered input output word frame call setup homes post
  intro current saved
  apply portable_small_prepare program method storage profile found original entered current input output word frame enteredWF homes saved post
  intro after state
  obtain ⟨lowHome, lowSlot, lowRead⟩ := state.limbs 0
  obtain ⟨sumHome, sumSlot, sumRead⟩ := state.sumRead
  apply portable_small_low_decision program method storage profile found after frame args lowHome sumHome
    (inputLimb original input 0) (inputLimb original input 0 + word) lowSlot sumSlot lowRead sumRead post
  split
  · rename_i carry
    apply state.increment program method storage profile found 0 args enteredWF homes post
    intro after1 state1
    split
    · rename_i first
      apply state1.increment program method storage profile found 1 args enteredWF homes post
      intro after2 state2
      split
      · rename_i second
        apply state2.increment program method storage profile found 2 args enteredWF homes post
        intro after3 state3
        split
        · rename_i third
          exact state3.exit program method storage profile found storageFound 4
            (portable_site_overflow _ word carry (by simpa [armIncrementWord] using first)
              (by simpa [armIncrementWord] using second) (by simpa [armIncrementWord] using third)) call setup
        · rename_i third
          exact state3.exit program method storage profile found storageFound 3
            (portable_site_third _ word carry (by simpa [armIncrementWord] using first)
              (by simpa [armIncrementWord] using second) (by simpa [armIncrementWord] using third)) call setup
      · rename_i second
        exact state2.exit program method storage profile found storageFound 2
          (portable_site_second _ word carry (by simpa [armIncrementWord] using first)
            (by simpa [armIncrementWord] using second)) call setup
    · rename_i first
      exact state1.exit program method storage profile found storageFound 1
        (portable_site_first _ word carry (by simpa [armIncrementWord] using first)) call setup
  · rename_i carry
    exact state.exit program method storage profile found storageFound 0
      (portable_site_no_carry _ word carry) call setup

/-- Ordinary valid caller views establish a checked invocation of the portable helper with exact sum and overflow. -/
theorem checked_portable_small_contract (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (disabled : profile.advSimd = false)
    (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method
        (armSmallArguments input output word) memory fuel final returned ∧
      ARMSmallPost memory final returned input output word := by
  let args := armSmallArguments input output word
  obtain ⟨frame, entered, setup, homes, _, _⟩ := portable_small_frame_setup profile storage memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    portable_small_entry program method storage profile found disabled storageFound memory entered input output word frame call setup homes
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, armSmallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method (portableSmallBody profile storage)
      args memory frame entered fuel final returned found checked setup live executed, result⟩

#print axioms PortableSmallState.exit
#print axioms portable_small_entry
#print axioms checked_portable_small_contract
end UInt256Proof.Add.Safety
