import UInt256.Methods.Add.Vector128ARMScalarPrefix
import UInt256.Methods.Add.ScalarSetup
import CIL.Safety.WordRoots
import UInt256.Safety.NumericStore

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- The extracted ARM dispatcher initializes the saved-reference root and the
    adjacent numeric home; their identities follow from actual frame setup. -/
theorem arm_scalar_slots (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (boundary : Nat) (frame : Frame)
    (homes : WordHomes memory boundary scalarLocalSpecs frame.locals) :
    frame.locals[7]? = some (.root (some .null)) ∧
    ∃ home, frame.locals[8]? = some (.bytes .word64 home) ∧
      boundary ≤ home.allocation ∧
      read memory home 8 1 = .ok (numberBytes 0 8) ∧
      access memory home 8 1 true = .ok () := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    refine ⟨homes.root_at 7 (by rfl), ?_⟩
    simpa using homes.word_at 8 (BitVec.ofNat 64 0) (by rfl)

/-- Reuse the original allocation evidence after the saved reference changes.
    This private write preserves caller bytes and access authority for later steps. -/
theorem arm_scalar_private_store (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (source : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary scalarLocalSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current) :
    ∃ home after,
      frame.locals[8]? = some (.bytes .word64 home) ∧
      read after home 8 1 = .ok (numberBytes word.toNat 8) ∧
      MemoryBelow boundary current after ∧
      CallingConditions Extracted.program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current home (numberBytes word.toNat 8) 1 = .ok after ∧
      ∀ pc args rest, step Extracted.addScalarBody (.setLocal 8) pc args
        (armScalarSavedFrame frame source) (.scalar (.i64 word) :: rest) current =
          .ok (.next (pc + 1) rest (armScalarSavedFrame frame source) after) := by
  obtain ⟨_, home, slot, bound, _, writable⟩ := arm_scalar_slots enabled entered boundary frame homes
  have actual : (armScalarSavedFrame frame source).locals[8]? = some (.bytes .word64 home) := by
    simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot
  obtain ⟨after, result⟩ := checked_numeric_home_store Extracted.program Extracted.addScalarBody
    boundary entered current inputs outputs (armScalarSavedFrame frame source) call enteredWF
    authority 8 ⟨.word64, .i64 0, 0, rfl⟩ home actual bound writable (.i64 word) word.toNat rfl
  exact ⟨home, after, slot, result⟩


/-- Compose entry dispatch, reference-root assignment, low-limb load and private
    store. The next decision sees unchanged caller bytes and initialized local8. -/
theorem arm_scalar_initial_prefix (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (left right : Reference)
    (call : CallingConditions Extracted.program entered inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary scalarLocalSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ home after,
      frame.locals[8]? = some (.bytes .word64 home) →
      read after home 8 1 = .ok (numberBytes (inputLimb entered right 0).toNat 8) →
      MemoryBelow boundary entered after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarIndex 7 args
          (armScalarSavedFrame frame left) [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 0 args frame [] entered =
        .ok (final, returned) ∧ post final returned := by
  have slots := arm_scalar_slots enabled entered boundary frame homes
  obtain ⟨home, after, slot, loaded, preserved, afterCall, authority, _, stored⟩ :=
    arm_scalar_private_store enabled boundary entered entered inputs outputs frame left
      (inputLimb entered right 0) call enteredWF homes ((MemoryBelow.refl _ _).accessBelow)
  apply arm_scalar_dispatch enabled entered frame args post
  apply arm_scalar_save_source enabled false entered frame args left (some .null)
    slots.1 leftArg (call.input_formed leftMember) post
  apply arm_scalar_low_load enabled false entered (armScalarSavedFrame frame left) args
    inputs outputs right call rightMember rightArg post
  have done := continuation home after slot loaded preserved afterCall authority
  have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
  first
  | solve | simp [Extracted.profile] at enabled
  | exact run_next_exists post found (by rfl) (stored 6 args []) done

#print axioms arm_scalar_initial_prefix

#print axioms arm_scalar_slots
#print axioms arm_scalar_private_store
end UInt256Proof.Add.Safety
