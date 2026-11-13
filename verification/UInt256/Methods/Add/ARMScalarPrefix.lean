import UInt256.Generated.MethodTemplates
import UInt256.Methods.Add.ARMSmallContract
import UInt256.Methods.Add.ARMFlag
import UInt256.Safety.Contract
import UInt256.Safety.CallerSetup
import UInt256.Methods.Add.ScalarReportingResult
import CIL.Safety.WordFrameSetup
import CIL.Safety.WordRoots
import UInt256.Safety.LimbAccess
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
def armScalarBody (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method1
      $(Lean.mkIdent `profile) true false $(Lean.mkIdent `smallIndex)
      $(Lean.mkIdent `vectorIndex) 0 0)) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

/-- Read the initializer recipe from extraction; frame setup rejects any initializer or kind
    outside the supported word/root recipe. -/
def armScalarLocalSpecs : List (Option (BitVec 64)) :=
  [some 0, some 0, some 0, some 0, some 0, some 0, some 0, none, some 0]

/-- Actual setup provides indexed readable/writable word homes, distinct fresh identities, and unchanged older caller storage. -/
theorem arm_scalar_frame_setup (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame (armScalarBody profile vectorIndex smallIndex) args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity armScalarLocalSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  word_frame_setup _ armScalarLocalSpecs (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    memory args wellFormed

/-- The frame after the dispatcher saves its selected operand reference in the root local. -/
def armScalarSavedFrame (frame : Frame) (source : Reference) : Frame :=
  { frame with locals := frame.locals.set 7 (.root (some (.address source))) }

/-- The extracted ARM dispatcher initializes the saved-reference root and the adjacent numeric home; their identities follow from actual frame setup. -/
theorem arm_scalar_slots (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (memory : Memory) (boundary : Nat) (frame : Frame)
    (homes : WordHomes memory boundary armScalarLocalSpecs frame.locals) :
    frame.locals[7]? = some (.root (some .null)) ∧
    ∃ home, frame.locals[8]? = some (.bytes .word64 home) ∧
      boundary ≤ home.allocation ∧
      read memory home 8 1 = .ok (numberBytes 0 8) ∧
      access memory home 8 1 true = .ok () := by
    refine ⟨homes.root_at 7 (by rfl), ?_⟩
    simpa using homes.word_at 8 (BitVec.ofNat 64 0) (by rfl)

/-- Reuse the original allocation evidence after the saved reference changes. -/
theorem arm_scalar_private_store (program : CIL.Program) (vectorIndex smallIndex : Nat)
    (profile : CIL.FeatureProfile) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (source : Reference) (word : BitVec 64)
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary armScalarLocalSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current) :
    ∃ home after,
      frame.locals[8]? = some (.bytes .word64 home) ∧
      read after home 8 1 = .ok (numberBytes word.toNat 8) ∧
      MemoryBelow boundary current after ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current home (numberBytes word.toNat 8) 1 = .ok after ∧
      ∀ pc args rest, step (armScalarBody profile vectorIndex smallIndex) (.setLocal 8) pc args
        (armScalarSavedFrame frame source) (.scalar (.i64 word) :: rest) current =
          .ok (.next (pc + 1) rest (armScalarSavedFrame frame source) after) := by
  obtain ⟨home, slot, bound, _, writable⟩ := homes.word_at 8 (BitVec.ofNat 64 0) (by rfl)
  have actual : (armScalarSavedFrame frame source).locals[8]? = some (.bytes .word64 home) := by
    simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot
  obtain ⟨after, result⟩ := checked_numeric_home_store program
    (armScalarBody profile vectorIndex smallIndex) boundary entered current inputs outputs
    (armScalarSavedFrame frame source) call enteredWF authority 8 ⟨.word64, .i64 0, 0, rfl⟩ home
    actual bound writable (.i64 word) word.toNat rfl
  exact ⟨home, after, slot, result⟩

/-- The or of an operand's three upper limbs, zero exactly when it fits one word. -/
def armScalarUpper (memory : Memory) (input : Reference) : BitVec 64 :=
  inputLimb memory input 1 ||| inputLimb memory input 2 ||| inputLimb memory input 3

/-- Where the dispatcher continues: right small, left small, or the vector helper. -/
def armScalarTarget (memory : Memory) (left right : Reference) : Nat :=
  if armScalarUpper memory right = BitVec.ofNat 64 0 then 36
  else if armScalarUpper memory left = BitVec.ofNat 64 0 then 31 else 25

/-- Actual entry through all operand decisions, carrying initialized private data and the caller footprint into every selected continuation. -/
theorem arm_scalar_dispatch_prefix (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (boundary : Nat) (entered : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (left right : Reference)
    (call : CallingConditions program entered inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary armScalarLocalSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ home after,
      frame.locals[8]? = some (.bytes .word64 home) →
      read after home 8 1 = .ok (numberBytes (inputLimb entered right 0).toNat 8) →
      MemoryBelow boundary entered after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run program fuel method (armScalarTarget after left right) args
          (armScalarSavedFrame frame left) [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨home, after, slot, loaded, preserved, afterCall, authority, _, stored⟩ :=
    arm_scalar_private_store program vectorIndex smallIndex profile boundary entered entered
      inputs outputs frame left (inputLimb entered right 0) call enteredWF homes
      (MemoryBelow.refl _ _).accessBelow
  have done := continuation home after slot loaded preserved afterCall authority
  have decided : ∃ fuel final returned, run program fuel method 7 args
      (armScalarSavedFrame frame left) [] after = .ok (final, returned) ∧
        post final returned := by
    have leftField := afterCall.input_field_instruction leftMember
    have rightField := afterCall.input_field_instruction rightMember
    unfold armScalarTarget armScalarUpper at done
    by_cases rightSmall : inputLimb after right 1 ||| inputLimb after right 2 |||
        inputLimb after right 3 = BitVec.ofNat 64 0 <;>
      by_cases leftSmall : inputLimb after left 1 ||| inputLimb after left 2 |||
        inputLimb after left 3 = BitVec.ofNat 64 0
    all_goals
      simp only [rightSmall, leftSmall, ite_true, ite_false] at done
      cil_contract_steps [found, leftArg, rightArg, afterCall.input_formed leftMember,
        afterCall.input_formed rightMember, leftField 1, leftField 2, leftField 3,
        rightField 1, rightField 2, rightField 3, rightSmall, leftSmall] until done
  have bodyProfile : (armScalarBody profile vectorIndex smallIndex).profile = profile := rfl
  cil_contract_steps [found, enabled, bodyProfile, CIL.FeatureProfile.evaluate, leftArg,
    rightArg, homes.root_at 7 (by rfl), call.input_formed leftMember,
    call.input_formed rightMember, call.input_field_instruction rightMember 0, stored,
    armScalarSavedFrame] until decided

/-- The left-small route replaces the saved source and low word, retaining original allocation evidence and preserving caller bytes throughout. -/
theorem arm_scalar_swap_prefix (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (boundary : Nat) (entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (left right : Reference)
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary armScalarLocalSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ home after,
      frame.locals[8]? = some (.bytes .word64 home) →
      read after home 8 1 = .ok (numberBytes (inputLimb current left 0).toNat 8) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run program fuel method 36 args
          (armScalarSavedFrame frame right) [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 31 args (armScalarSavedFrame frame left)
        [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨home, after, slot, loaded, preserved, afterCall, afterAuthority, _, stored⟩ :=
    arm_scalar_private_store program vectorIndex smallIndex profile boundary entered current
      inputs outputs frame right (inputLimb current left 0) call enteredWF homes authority
  have done := continuation home after slot loaded preserved afterCall afterAuthority
  have root : (armScalarSavedFrame frame left).locals[7]? =
      some (.root (some (.address left))) := by
    simp only [armScalarSavedFrame, List.getElem?_set_self', homes.root_at 7 (by rfl)]
    rfl
  cil_contract_steps [found, leftArg, rightArg, root, call.input_formed leftMember,
    call.input_formed rightMember, call.input_field_instruction leftMember 0, stored,
    armScalarSavedFrame, List.set_set] until done

end UInt256Proof.Add.Safety