import UInt256.Methods.Add.ARMSmallContract
import UInt256.Methods.Add.ARMFlag
import UInt256.Safety.Contract
import UInt256.Safety.CallerSetup
import UInt256.Methods.Add.ScalarReportingResult
import CIL.Safety.WordHomes
import CIL.Safety.WordRoots
import UInt256.Safety.LimbAccess
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
def armScalarBody (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .nullRef, .i64 0], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .word64, .reference, .word64], parameterHomes := [], staticSites := [], code := [
  .feature .advSimd,
  .brzero 41,
  .arg 0,
  .setLocal 7,
  .arg 1,
  .fieldAt 0 8,
  .setLocal 8,
  .arg 1,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 16 8,
  .bor,
  .arg 1,
  .fieldAt 24 8,
  .bor,
  .brzero 36,
  .arg 0,
  .fieldAt 8 8,
  .arg 0,
  .fieldAt 16 8,
  .bor,
  .arg 0,
  .fieldAt 24 8,
  .bor,
  .brzero 31,
  .arg 0,
  .arg 1,
  .arg 2,
  .arg 3 (some .unsigned8),
  .call vectorIndex 4,
  .ret (some .unsigned8),
  .arg 1,
  .setLocal 7,
  .arg 0,
  .fieldAt 0 8,
  .setLocal 8,
  .local 7,
  .local 8,
  .arg 2,
  .call smallIndex 3,
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
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

/-- The actual scalar dispatcher's vector call and forwarding return use the independently certified helper and its proved scalar result shape. -/
theorem vector128_arm_parent_call (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (vectorFound : program[vectorIndex]? = some (armBody profile)) (enabled : profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (post : Memory → List Value → Prop)
    (continuation : ∀ childFuel final returnedFlag,
      InvocationCertificate program vectorIndex (vector128Arguments left right output flag)
        memory childFuel
        final [.scalar (.i32 returnedFlag)] →
      inputValue final output = inputValue memory left + inputValue memory right →
      (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) →
      access final output 32 1 true = .ok () →
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) →
      post (leaveFrame frame final) [.scalar (.i32 returnedFlag)]) :
    ∃ fuel final returned,
      run program fuel method 25 (vector128Arguments left right output flag)
        frame [] memory = .ok (final, returned) ∧ post final returned := by
    obtain ⟨childFuel, final, returnedFlag, certified, result, returnedFit, overflow, writable, footprint⟩ :=
      arm_helper_checked_with_flag profile enabled program vectorIndex vectorFound memory left right output flag flagFit call
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    have fetched : (armScalarBody profile vectorIndex smallIndex).code[29]? = some (.call vectorIndex 4) := by rfl
    have stepped : step (armScalarBody profile vectorIndex smallIndex) (.call vectorIndex 4) 29
        (vector128Arguments left right output flag) frame
        [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (.call vectorIndex (vector128Arguments left right output flag) [] memory) := by
      simp [step, cil_guard, observerCount, flagFit, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have returned : run program 1 method 30
        (vector128Arguments left right output flag) frame [.scalar (.i32 returnedFlag)] final =
        .ok (leaveFrame frame final, [.scalar (.i32 returnedFlag)]) := by
      simp [run, found, armScalarBody, step, cil_guard, observerCount, returnedFit, List.mapM, Option.bind, checkedValue, numericValue, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      rfl
    obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨_, certified.1⟩ ⟨1, returned⟩
    have done := continuation childFuel final returnedFlag certified result overflow writable footprint
    have finish : ∃ fuel final returned,
        run program fuel method 29 (vector128Arguments left right output flag)
          frame [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
          .ok (final, returned) ∧ post final returned := ⟨fuel, _, _, executed, done⟩
    repeat' first
      | exact finish
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, cil_guard, observerCount, flagFit, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_parent_call
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety

open CIL.Safety

/-- Read the initializer recipe from extraction; the checked metadata equations below reject any initializer or kind outside the supported word/root recipe. -/
def armScalarLocalSpecs : List (Option (BitVec 64)) := [some 0, some 0, some 0, some 0, some 0, some 0, some 0, none, some 0]

theorem arm_scalar_local_metadata (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) :
    (armScalarBody profile vectorIndex smallIndex).localKinds = wordKinds armScalarLocalSpecs ∧
    (armScalarBody profile vectorIndex smallIndex).locals = wordInitializers armScalarLocalSpecs := by
  simp [armScalarLocalSpecs, wordKinds, wordInitializers, armScalarBody]

/-- Actual setup provides indexed readable/writable word homes, distinct fresh identities, and unchanged older caller storage. -/
theorem arm_scalar_frame_setup (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame (armScalarBody profile vectorIndex smallIndex) args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity armScalarLocalSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨slots, owned, result, made, homes⟩ := make_word_locals memory memory.nextIdentity armScalarLocalSpecs wellFormed
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have entered : enterFrame (armScalarBody profile vectorIndex smallIndex) args memory = .ok (frame, result) := by
    unfold enterFrame
    dsimp only
    rw [(arm_scalar_local_metadata profile vectorIndex smallIndex).1, (arm_scalar_local_metadata profile vectorIndex smallIndex).2,
      show (armScalarBody profile vectorIndex smallIndex).opaqueVectorLocals = [] from rfl, makeSelectedLocals, List.isEmpty_nil, if_pos rfl, made]
    simp only [Bind.bind, Except.bind, armScalarBody, makeArgumentHomes, makeParameterHomes, Pure.pure, Except.pure, List.map_nil, List.append_nil]
    rfl
  exact ⟨frame, result, entered, homes, enterFrame_preserves_caller_memory _ _ _ _ _ entered,
    enterFrame_preserves_wellFormed _ _ _ _ _ wellFormed entered⟩

#print axioms arm_scalar_local_metadata
#print axioms arm_scalar_frame_setup

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armScalarSavedFrame (frame : Frame) (source : Reference) : Frame :=
  { frame with locals := frame.locals.set 7 (.root (some (.address source))) }

/-- Check the initial ARM feature guard before touching caller references. -/
theorem arm_scalar_dispatch (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method 2 args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] memory = .ok (final, returned) ∧ post final returned := by
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, cil_guard, observerCount, armScalarBody, enabled, pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Both selected source-reference assignments update a tracked root, without changing caller memory or any numeric local home. -/
theorem arm_scalar_save_source (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true) (swapped : Bool) (memory : Memory) (frame : Frame)
    (args : List Value) (source : Reference) (initial : Option ManagedReference)
    (slot : frame.locals[7]? = some (.root initial))
    (argument : args[if swapped then 1 else 0]? = some (.reference (.address source)))
    (formed : form memory source = .ok source) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (if swapped then 33 else 4)
        args (armScalarSavedFrame frame source) [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (if swapped then 31 else 2)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
    cases swapped <;> simp only [Bool.false_eq_true, ite_false, ite_true] at argument continuation ⊢
    all_goals
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, argument, slot, storeLocal, armScalarSavedFrame, checkedValue, formValue, formed,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- The selected low-word load is checked against the caller's input view. -/
theorem arm_scalar_low_load (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true) (swapped : Bool) (memory : Memory) (frame : Frame)
    (args : List Value) (inputs outputs : List Reference) (input : Reference)
    (call : CallingConditions program memory inputs outputs) (member : input ∈ inputs)
    (argument : args[if swapped then 0 else 1]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (if swapped then 35 else 6)
        args frame [.scalar (.i64 (inputLimb memory input 0))] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (if swapped then 33 else 4)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
    have formed := call.input_formed member
    have loaded := call.input_field_instruction member 0
    dsimp at loaded
    cases swapped <;> simp only [Bool.false_eq_true, ite_false, ite_true] at argument continuation ⊢
    all_goals
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, argument, checkedValue, formValue, formed, loaded, pureArity,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Saving the selected root preserves the distinct numeric local used for the small operand. -/
theorem arm_scalar_word_store (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) (frame : Frame) (source home : Reference)
    (memory : Memory) (word : BitVec 64) (pc : Nat) (args rest : List Value)
    (slot : frame.locals[8]? = some (.bytes .word64 home))
    (ready : access memory home 8 1 true = .ok ()) :
    ∃ result,
      step (armScalarBody profile vectorIndex smallIndex) (.setLocal 8) pc args (armScalarSavedFrame frame source)
        (.scalar (.i64 word) :: rest) memory =
          .ok (.next (pc + 1) rest (armScalarSavedFrame frame source) result) ∧
      write memory home (numberBytes word.toNat 8) 1 = .ok result ∧
      read result home 8 1 = .ok (numberBytes word.toNat 8) := by
  apply step_store_word64_same_frame word ?_ ready
  simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot

/-- Both upper-limb tests read the original caller view through checked field instructions. -/
theorem arm_scalar_upper_loads (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (leftTest : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (inputs outputs : List Reference) (input : Reference)
    (call : CallingConditions program memory inputs outputs) (member : input ∈ inputs)
    (argument : args[if leftTest then 0 else 1]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (if leftTest then 24 else 15)
        args frame [.scalar (.i64 (inputLimb memory input 1 ||| inputLimb memory input 2 |||
          inputLimb memory input 3))] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (if leftTest then 16 else 7)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
    have formed := call.input_formed member
    have loaded := call.input_field_instruction member
    have l1 := loaded 1
    have l2 := loaded 2
    have l3 := loaded 3
    dsimp at l1 l2 l3
    simp only [show (3 : Fin 4).val = 3 from rfl] at l3
    cases leftTest <;> simp only [Bool.false_eq_true, ite_false, ite_true] at argument continuation ⊢
    all_goals
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, argument, checkedValue, numericValue, formValue, formed, l1, l2, l3, pureArity,
               pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.binary,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Follow the actual right/left small-operand branch, without assuming its outcome or discarding either continuation. -/
theorem arm_scalar_upper_branch (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (leftTest : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (condition : BitVec 64) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method
        (if condition = BitVec.ofNat 64 0 then (if leftTest then 31 else 36)
         else (if leftTest then 25 else 16))
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (if leftTest then 24 else 15)
        args frame [.scalar (.i64 condition)] memory = .ok (final, returned) ∧ post final returned := by
    cases leftTest <;> by_cases zero : condition = BitVec.ofNat 64 0
    all_goals
      simp only [Bool.false_eq_true, ite_false, ite_true, zero] at continuation ⊢
      apply run_next_exists post found (by rfl) _ continuation
      simp [step, cil_guard, observerCount, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.truth,
        show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, zero,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms arm_scalar_upper_branch

#print axioms arm_scalar_word_store
#print axioms arm_scalar_upper_loads

#print axioms arm_scalar_dispatch
#print axioms arm_scalar_save_source
#print axioms arm_scalar_low_load
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

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
theorem arm_scalar_private_store (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (boundary : Nat) (entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (source : Reference) (word : BitVec 64)
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
  obtain ⟨_, home, slot, bound, _, writable⟩ := arm_scalar_slots program method vectorIndex smallIndex profile found enabled entered boundary frame homes
  have actual : (armScalarSavedFrame frame source).locals[8]? = some (.bytes .word64 home) := by
    simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot
  obtain ⟨after, result⟩ := checked_numeric_home_store program (armScalarBody profile vectorIndex smallIndex)
    boundary entered current inputs outputs (armScalarSavedFrame frame source) call enteredWF
    authority 8 ⟨.word64, .i64 0, 0, rfl⟩ home actual bound writable (.i64 word) word.toNat rfl
  exact ⟨home, after, slot, result⟩

/-- Compose entry dispatch, reference-root assignment, low-limb load and private store. -/
theorem arm_scalar_initial_prefix (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
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
        run program fuel method 7 args
          (armScalarSavedFrame frame left) [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered =
        .ok (final, returned) ∧ post final returned := by
  have slots := arm_scalar_slots program method vectorIndex smallIndex profile found enabled entered boundary frame homes
  obtain ⟨home, after, slot, loaded, preserved, afterCall, authority, _, stored⟩ :=
    arm_scalar_private_store program method vectorIndex smallIndex profile found enabled boundary entered entered inputs outputs frame left
      (inputLimb entered right 0) call enteredWF homes ((MemoryBelow.refl _ _).accessBelow)
  apply arm_scalar_dispatch program method vectorIndex smallIndex profile found enabled entered frame args post
  apply arm_scalar_save_source program method vectorIndex smallIndex profile found enabled false entered frame args left (some .null)
    slots.1 leftArg (call.input_formed leftMember) post
  apply arm_scalar_low_load program method vectorIndex smallIndex profile found enabled false entered (armScalarSavedFrame frame left) args
    inputs outputs right call rightMember rightArg post
  have done := continuation home after slot loaded preserved afterCall authority
  exact run_next_exists post found (by rfl) (stored 6 args []) done

#print axioms arm_scalar_initial_prefix

#print axioms arm_scalar_slots
#print axioms arm_scalar_private_store
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armScalarUpper (memory : Memory) (input : Reference) : BitVec 64 :=
  inputLimb memory input 1 ||| inputLimb memory input 2 ||| inputLimb memory input 3

def armScalarTarget (memory : Memory) (left right : Reference) : Nat :=
  if armScalarUpper memory right = BitVec.ofNat 64 0 then 36
  else if armScalarUpper memory left = BitVec.ofNat 64 0 then 31 else 25

/-- Both operand tests are followed in order, preserving all memory and locals. -/
theorem arm_scalar_decisions (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (inputs outputs : List Reference)
    (left right : Reference) (call : CallingConditions program memory inputs outputs)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (armScalarTarget memory left right)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 7 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  unfold armScalarTarget at continuation
  apply arm_scalar_upper_loads program method vectorIndex smallIndex profile found enabled false memory frame args inputs outputs right
    call rightMember rightArg post
  apply arm_scalar_upper_branch program method vectorIndex smallIndex profile found enabled false memory frame args (armScalarUpper memory right) post
  by_cases small : armScalarUpper memory right = BitVec.ofNat 64 0
  · simpa only [small, Bool.false_eq_true, ite_false, ite_true] using continuation
  · simp only [small, ite_false, Bool.false_eq_true] at *
    apply arm_scalar_upper_loads program method vectorIndex smallIndex profile found enabled true memory frame args inputs outputs left
      call leftMember leftArg post
    apply arm_scalar_upper_branch program method vectorIndex smallIndex profile found enabled true memory frame args (armScalarUpper memory left) post
    simpa only [small,  ite_false, ite_true] using continuation

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
  apply arm_scalar_initial_prefix program method vectorIndex smallIndex profile found enabled boundary entered inputs outputs frame args left right
    call enteredWF homes leftMember rightMember leftArg rightArg post
  intro home after slot loaded preserved afterCall authority
  exact arm_scalar_decisions program method vectorIndex smallIndex profile found enabled after (armScalarSavedFrame frame left) args inputs outputs
    left right afterCall leftMember rightMember leftArg rightArg post
    (continuation home after slot loaded preserved afterCall authority)

#print axioms arm_scalar_decisions
#print axioms arm_scalar_dispatch_prefix
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem arm_scalar_saved_replace (frame : Frame) (first second : Reference) :
    armScalarSavedFrame (armScalarSavedFrame frame first) second =
      armScalarSavedFrame frame second := by
  simp [armScalarSavedFrame, List.set_set]

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
  have slots := arm_scalar_slots program method vectorIndex smallIndex profile found enabled entered boundary frame homes
  have root : (armScalarSavedFrame frame left).locals[7]? = some (.root (some (.address left))) := by
    simp only [armScalarSavedFrame, List.getElem?_set_self', slots.1]
    rfl
  obtain ⟨home, after, slot, loaded, preserved, afterCall, afterAuthority, _, stored⟩ :=
    arm_scalar_private_store program method vectorIndex smallIndex profile found enabled boundary entered current inputs outputs frame right
      (inputLimb current left 0) call enteredWF homes authority
  apply arm_scalar_save_source program method vectorIndex smallIndex profile found enabled true current (armScalarSavedFrame frame left) args right
    (some (.address left)) root rightArg (call.input_formed rightMember) post
  rw [arm_scalar_saved_replace]
  apply arm_scalar_low_load program method vectorIndex smallIndex profile found enabled true current (armScalarSavedFrame frame right) args
    inputs outputs left call leftMember leftArg post
  have done := continuation home after slot loaded preserved afterCall afterAuthority
  exact run_next_exists post found (by rfl) (stored 35 args []) done

/-- Load the selected small-helper arguments from the tracked root and initialized numeric home, checking both managed references before the call. -/
theorem arm_scalar_small_arguments (program : CIL.Program) (method vectorIndex smallIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armScalarBody profile vectorIndex smallIndex)) (enabled : profile.advSimd = true)
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
      run program fuel method 39 args frame
        [.reference (.address output), .scalar (.i64 word), .reference (.address source)] memory =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 36 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
    have wordLoad := fun (pc : Nat) (stack : List Value) => step_load_word64
      (body := (armScalarBody profile vectorIndex smallIndex)) (pc := pc) (args := args) (stack := stack) slot loaded
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact wordLoad _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, root, loadLocal, outputArg, checkedValue, formValue, sourceFormed, outputFormed,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms arm_scalar_small_arguments

#print axioms arm_scalar_saved_replace
#print axioms arm_scalar_swap_prefix
end UInt256Proof.Add.Safety
