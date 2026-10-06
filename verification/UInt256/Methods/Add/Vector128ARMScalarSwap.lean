import UInt256.Methods.Add.Vector128ARMScalarDecision

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

theorem arm_scalar_saved_replace (frame : Frame) (first second : Reference) :
    armScalarSavedFrame (armScalarSavedFrame frame first) second =
      armScalarSavedFrame frame second := by
  simp [armScalarSavedFrame, List.set_set]

/-- The left-small route replaces the saved source and low word, retaining
    original allocation evidence and preserving caller bytes throughout. -/
theorem arm_scalar_swap_prefix (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (left right : Reference)
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary scalarLocalSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ home after,
      frame.locals[8]? = some (.bytes .word64 home) →
      read after home 8 1 = .ok (numberBytes (inputLimb current left 0).toNat 8) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarIndex 36 args
          (armScalarSavedFrame frame right) [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 31 args (armScalarSavedFrame frame left)
        [] current = .ok (final, returned) ∧ post final returned := by
  have slots := arm_scalar_slots enabled entered boundary frame homes
  have root : (armScalarSavedFrame frame left).locals[7]? = some (.root (some (.address left))) := by
    simp only [armScalarSavedFrame, List.getElem?_set_self', slots.1]
    rfl
  obtain ⟨home, after, slot, loaded, preserved, afterCall, afterAuthority, _, stored⟩ :=
    arm_scalar_private_store enabled boundary entered current inputs outputs frame right
      (inputLimb current left 0) call enteredWF homes authority
  apply arm_scalar_save_source enabled true current (armScalarSavedFrame frame left) args right
    (some (.address left)) root rightArg (call.input_formed rightMember) post
  rw [arm_scalar_saved_replace]
  apply arm_scalar_low_load enabled true current (armScalarSavedFrame frame right) args
    inputs outputs left call leftMember leftArg post
  have done := continuation home after slot loaded preserved afterCall afterAuthority
  have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
  first
  | solve | simp [Extracted.profile] at enabled
  | exact run_next_exists post found (by rfl) (stored 35 args []) done


/-- Load the selected small-helper arguments from the tracked root and initialized
    numeric home, checking both managed references before the call. -/
theorem arm_scalar_small_arguments (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (source output home : Reference)
    (word : BitVec 64)
    (root : frame.locals[7]? = some (.root (some (.address source))))
    (slot : frame.locals[8]? = some (.bytes .word64 home))
    (loaded : read memory home 8 1 = .ok (numberBytes word.toNat 8))
    (sourceFormed : form memory source = .ok source)
    (outputArg : args[2]? = some (.reference (.address output)))
    (outputFormed : form memory output = .ok output)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 39 args frame
        [.reference (.address output), .scalar (.i64 word), .reference (.address source)] memory =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 36 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    have wordLoad := fun (pc : Nat) (stack : List Value) => step_load_word64
      (body := Extracted.addScalarBody) (pc := pc) (args := args) (stack := stack) slot loaded
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact wordLoad _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, root, loadLocal, outputArg, checkedValue, formValue, sourceFormed, outputFormed,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms arm_scalar_small_arguments

#print axioms arm_scalar_saved_replace
#print axioms arm_scalar_swap_prefix
end UInt256Proof.Add.Safety
