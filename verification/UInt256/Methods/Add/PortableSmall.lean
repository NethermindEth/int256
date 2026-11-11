import UInt256.Generated.MethodTemplates
import CIL.Safety.Equations
import UInt256.Methods.Add.ARMSmallContract
import UInt256.Methods.Add.InputWords
import CIL.Safety.MethodContract
import CIL.Safety.WeakestPrecondition

/-! Checked scalar addition preserves saved inputs across private stores and limb helper calls. -/

namespace UInt256Proof.Add.Safety

open CIL.Safety

-- AddScalarUInt64 with the AdvSimd branch disabled: one store and constant flag per carry exit.
def portableSmallBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method2
      $(Lean.mkIdent `profile) false $(Lean.mkIdent `storage))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem portable_small_frame_setup (profile : CIL.FeatureProfile) (storage : Nat) (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame (portableSmallBody profile storage) args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity armSmallSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup (portableSmallBody profile storage) armSmallSpecs (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) memory args wf

/-- Store the output limbs through StoreLimbs and return the flag: limbs and flag that are the
    small-sum result give the exact sum, the overflow bit and the caller footprint. -/
theorem portable_small_exit (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (portableSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (original entered current : Memory) (input output : Reference) (word : BitVec 64)
    (frame : Frame) (call : CallingConditions program original [input] [output])
    (setup : enterFrame (portableSmallBody profile storage)
      (armSmallArguments input output word) original = .ok (frame, entered))
    (currentCall : CallingConditions program current [input] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (callPc : Nat) (second third fourth : BitVec 64) (flag : BitVec 32)
    (callAt : (portableSmallBody profile storage).code[callPc]? = some (.call storage 5))
    (constAt : (portableSmallBody profile storage).code[callPc + 1]? = some (.const32 flag))
    (retAt : (portableSmallBody profile storage).code[callPc + 1 + 1]? =
      some (.ret (some .unsigned8)))
    (agrees : (armSmallResult (inputLimb original input) word).1 1 = second ∧
      (armSmallResult (inputLimb original input) word).1 2 = third ∧
      (armSmallResult (inputLimb original input) word).1 3 = fourth ∧
      (armSmallResult (inputLimb original input) word).2 = flag) :
    WP (Execution (fun fuel => run program fuel method callPc
        (armSmallArguments input output word) frame
        [.scalar (.i64 fourth), .scalar (.i64 third), .scalar (.i64 second),
          .scalar (.i64 (inputLimb original input 0 + word)), .reference (.address output)]
        current))
      (fun result => ARMSmallPost original result.1 result.2 input output word) := by
  obtain ⟨childFuel, stored, invoked, valid, outside, _, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract profile program storage
      storageFound current [input] output (inputLimb original input 0 + word) second third fourth
      currentCall
  have formed := currentCall.output_formed (by simp : output ∈ [output])
  have stepped : step (portableSmallBody profile storage) (.call storage 5) callPc
      (armSmallArguments input output word) frame
      [.scalar (.i64 fourth), .scalar (.i64 third), .scalar (.i64 second),
        .scalar (.i64 (inputLimb original input 0 + word)), .reference (.address output)]
      current = .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output
        (inputLimb original input 0 + word) second third fourth) [] current) := by
    cil_checked_step [UInt256Proof.Multiply.LimbStorage.arguments, formed]
  have flagFit : CIL.NarrowKind.unsigned8.extend flag = flag := by
    rw [← agrees.2.2.2, arm_small_result_flag]
    split <;> rfl
  apply WP.call (helperPost := fun result => result.1 = stored ∧ result.2 = [])
    found callAt stepped ⟨childFuel, (stored, []), invoked, rfl, rfl⟩
  rintro final values ⟨rfl, rfl⟩
  cil_contract_steps [found, constAt, retAt, flagFit]
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retired := leaveFrame_preserves_memory_below frame final original.nextIdentity
    (fun id member => (fresh.2 id member).1)
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame final).cells output.allocation offset).bits) =
      (fun offset => (final.cells output.allocation offset).bits) := by
    funext offset
    rw [retired.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have mathematical := arm_small_result_value original input word
    simp only [UInt256Model.value, armSmallOutputWords, agrees] at mathematical
    simpa only [inputValue, bytes] using value.trans mathematical
  · have initial : UInt256Model.value (inputLimb original input) = inputValue original input :=
      UInt256Proof.input_value (fun offset => (original.cells input.allocation offset).bits)
        input.offset
    rw [← agrees.2.2.2, arm_small_result_flag, initial]
  · exact (retired.access output outputOld 32 1 true).trans
      (valid.1.writable (wordView output) (by simp))
  · intro id old offset untouched
    exact (retired.cells id old offset).trans
      ((outside id offset untouched).trans (preserved.cells id old offset))
/-- Full portable helper execution: input snapshots, low sum, every carry exit, and the shared
    postcondition. -/
theorem portable_small_entry (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (portableSmallBody profile storage))
    (disabled : profile.advSimd = false)
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (portableSmallBody profile storage)
      (armSmallArguments input output word) original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    WP (Execution (fun fuel => run program fuel method 0
        (armSmallArguments input output word) frame [] entered))
      (fun result => ARMSmallPost original result.1 result.2 input output word) := by
  have enteredCall := call.after_frame_setup setup
  have valid := enteredCall.1
  have world := enteredCall.2
  have enteredFormed := valid.1
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have snapshots := LocalSnapshots.empty entered frame.locals
  have limbs := fun current below =>
    call.input_words_kept (current := current) below input (by simp)
  have exit := fun current => portable_small_exit program method storage profile found
    storageFound original entered current input output word frame call setup
  cil_contract_steps (snapshots := snapshots) [found, armSmallArguments, limbs _ preserved]
  have world := write_preserves_static_world _ _ _ _ _ _ world localWrite
  cil_contract_steps (snapshots := localSnapshots) [found, armSmallArguments, limbs _ preserved]
  have world := write_preserves_static_world _ _ _ _ _ _ world localWrite_1
  cil_contract_steps (snapshots := localSnapshots_1) [found, armSmallArguments, limbs _ preserved]
  have world := write_preserves_static_world _ _ _ _ _ _ world localWrite_2
  cil_contract_steps (snapshots := localSnapshots_2)
    [found, armSmallArguments, disabled, limbs _ preserved]
  have world := write_preserves_static_world _ _ _ _ _ _ world localWrite_3
  have world := write_preserves_static_world _ _ _ _ _ _ world localWrite_4
  split
  next carry =>
    cil_contract_steps (snapshots := localSnapshots_4) [found, armSmallArguments]
    have world := write_preserves_static_world _ _ _ _ _ _ world localWrite_5
    split
    next first =>
      have done := exit storedLocal_5 ⟨valid, world⟩ preserved 82 _ _ _ 0 (by rfl) (by rfl) (by rfl)
        (by simp [armSmallResult, armCarryResult, armIncrementWord, carry, first]
            exact ⟨rfl, rfl, rfl⟩)
      cil_contract_steps (snapshots := localSnapshots_5) [found, armSmallArguments] until done
    next first =>
      replace first := Decidable.not_not.mp first
      cil_contract_steps (snapshots := localSnapshots_5) [found, armSmallArguments]
      have world := write_preserves_static_world _ _ _ _ _ _ world localWrite_6
      split
      next second =>
        have done := exit storedLocal_6 ⟨valid, world⟩ preserved 98 _ _ _ 0 (by rfl) (by rfl)
          (by rfl) (by
            simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second]
            exact ⟨rfl, rfl, rfl⟩)
        cil_contract_steps (snapshots := localSnapshots_6) [found, armSmallArguments] until done
      next second =>
        replace second := Decidable.not_not.mp second
        cil_contract_steps (snapshots := localSnapshots_6) [found, armSmallArguments]
        have world := write_preserves_static_world _ _ _ _ _ _ world localWrite_7
        have lastIndex : (3 : Fin 4).val = 3 := rfl
        split
        next third =>
          have done := exit storedLocal_7 ⟨valid, world⟩ preserved 115 _ _ _ 0 (by rfl) (by rfl)
            (by rfl) (by
              simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second,
                third, lastIndex]
              exact ⟨rfl, rfl, rfl⟩)
          cil_contract_steps (snapshots := localSnapshots_7) [found, armSmallArguments] until done
        next third =>
          replace third := Decidable.not_not.mp third
          have done := exit storedLocal_7 ⟨valid, world⟩ preserved 126 _ _ _ 1 (by rfl) (by rfl)
            (by rfl) (by
              simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second,
                third, lastIndex]
              exact ⟨rfl, rfl, rfl⟩)
          cil_contract_steps (snapshots := localSnapshots_7) [found, armSmallArguments] until done
  next carry =>
    have done := exit storedLocal_4 ⟨valid, world⟩ preserved 67 _ _ _ 0 (by rfl) (by rfl) (by rfl)
      (by simp [armSmallResult, carry]; exact ⟨rfl, rfl, rfl⟩)
    cil_contract_steps (snapshots := localSnapshots_4) [found, armSmallArguments] until done
/-- Ordinary valid caller views establish a checked invocation of the portable helper with exact sum and overflow. -/
theorem checked_portable_small_contract (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (portableSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (disabled : profile.advSimd = false)
    (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method
        (armSmallArguments input output word) memory fuel final returned ∧
      ARMSmallPost memory final returned input output word := by
  let args := armSmallArguments input output word
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    portable_small_frame_setup profile storage memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    WP.adequate.mp (portable_small_entry program method storage profile found disabled
      storageFound memory entered input output word frame call setup homes)
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, armSmallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method (portableSmallBody profile storage)
      args memory frame entered fuel final returned found checked setup live executed, result⟩

end UInt256Proof.Add.Safety
