import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.ARMBody
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
theorem vector128_arm_entry_with_flag (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startCode : CodeAt body 0 vector128AddPrefix)
    (incomingCode : CodeAt body 0 (incomingPrefix body.profile.advSimd))
    (correctionCodeFound : CodeAt body 62 correctionCode)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (earlyCode : CodeAt body 69 (earlyOutputCode body.profile.advSimd))
    (propCode : CodeAt body 82 (propagationCode))
    (decisionCodeFound : CodeAt body 94 (decisionCode body.profile.advSimd))
    (fastCode : CodeAt body 204 (fastOutputCode body.profile.advSimd))
    (returns : body.returnsValue = true)
    (repairDispatchCode : CodeAt body 111 ([.feature .advSimd, .brzero 162]))
    (repairCode : CodeAt body 113 (armRepairCode))
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec) (enabled : body.profile.advSimd = true) (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    : ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧ CIL.NarrowKind.unsigned8.extend returnedFlag = returnedFlag ∧
        (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
          if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  by_cases fast : selectedPropagation128 body.profile.advSimd flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) = BitVec.ofNat 128 0
  · obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
      vector128_fast_entry program body method specs found startCode incomingCode correctionCodeFound firstFourteen sse ssse earlyCode propCode decisionCodeFound fastCode returns original entered inputs outputs left right output frame slots args
        call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagFit flagArg fast
    exact ⟨fuel, final, returned, executed, ⟨_, scalar, (by split <;> rfl), fun reporting => vector128_snapshot_fast_flag body.profile.advSimd original left right flag reporting fast⟩,
      result, writable, outside⟩
  · let post : Memory → List Value → Prop := fun final returned =>
      (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧ CIL.NarrowKind.unsigned8.extend returnedFlag = returnedFlag ∧
        (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
          if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset)
    apply vector128_dispatch_checked program body method specs found startCode incomingCode correctionCodeFound firstFourteen sse ssse earlyCode propCode decisionCodeFound original entered inputs outputs left right output frame slots args
      call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagFit flagArg post
    intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced _callerPreserved
    simp only [fast, ite_false]
    apply vector128_repair_dispatch program body method found repairDispatchCode current (vector128SavedFrame frame slots right) args post
    simp only [vector128RepairStart, enabled, ite_true]
    have extended : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read current reference 16 1 = .ok (numberBytes (vector128DecisionValues body.profile.advSimd original left right flag i).toNat 16) := by
      intro i
      by_cases within : i.val < 13
      · obtain ⟨reference, slot, loaded⟩ := snapshots ⟨i.val, within⟩
        refine ⟨reference, slot, ?_⟩
        simpa only [vector128DecisionValues, dite_eq_left within] using loaded
      · have same : i = 13 := by omega
        subst i
        exact ⟨conditionHome, conditionSlot, conditionRead⟩
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
      vector128_arm_repair_run program body method specs found repairCode repairSpecs firstFourteen returns enabled original entered current inputs outputs left right output
        (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args
        call currentCall (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
        outputMember outputArg flag flagFit flagArg extended (earlyRead enabled).1
        (fun id member => (fresh.2 id member).1)
    exact ⟨fuel, final, returned, executed, ⟨_, scalar, (by split <;> rfl), fun _ => rfl⟩, result, writable,
      fun id offset bound untouched => (outside id offset bound untouched).trans (footprint id offset bound untouched)⟩

theorem checked_vector128_arm_contract_with_flag (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startCode : CodeAt body 0 vector128AddPrefix)
    (incomingCode : CodeAt body 0 (incomingPrefix body.profile.advSimd))
    (correctionCodeFound : CodeAt body 62 correctionCode)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (earlyCode : CodeAt body 69 (earlyOutputCode body.profile.advSimd))
    (propCode : CodeAt body 82 (propagationCode))
    (decisionCodeFound : CodeAt body 94 (decisionCode body.profile.advSimd))
    (fastCode : CodeAt body 204 (fastOutputCode body.profile.advSimd))
    (returns : body.returnsValue = true)
    (repairDispatchCode : CodeAt body 111 ([.feature .advSimd, .brzero 162]))
    (repairCode : CodeAt body 113 (armRepairCode))
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)
    (metadata : body.localKinds = .reference :: specs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: specs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (opaqueLocals : body.opaqueVectorLocals = []) (enabled : body.profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      CIL.NarrowKind.unsigned8.extend returned = returned ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, slots, setup, layout, homes, preserved, enteredWF⟩ :=
    vector128_frame_setup body specs metadata vectors parameters opaqueLocals memory args call.1.1
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, footprint⟩ :=
    vector128_arm_entry_with_flag program body method specs found startCode incomingCode correctionCodeFound firstFourteen sse ssse earlyCode propCode decisionCodeFound fastCode returns repairDispatchCode repairCode repairSpecs enabled memory entered [left, right] [output] left right output frame slots args
      call setup layout homes (by simp) (by simp) (by simp) rfl rfl rfl flag flagFit rfl
  obtain ⟨returnedValue, rfl, returnedFit, overflow⟩ := scalar
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returnedValue,
    certify_invocation program method body args memory frame entered
      fuel final [.scalar (.i32 returnedValue)] found checked setup live executed,
    result, returnedFit, overflow, writable, footprint⟩

theorem arm_helper_checked_with_flag (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true)
    (program : CIL.Program) (method : Nat) (found : program[method]? = some (armBody profile))
    (memory : Memory) (left right output : Reference) (flag : BitVec 32)
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      CIL.NarrowKind.unsigned8.extend returned = returned ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let b := armBody profile
  have disabledFalse (disabled : b.profile.advSimd = false) : False := by
    change profile.advSimd = false at disabled
    rw [enabled] at disabled
    contradiction
  apply checked_vector128_arm_contract_with_flag program b method armSpecs found
    rfl (by simp only [b, armBody, incomingPrefix, enabled, ite_true]; rfl)
    rfl armSpecs_first (fun disabled => (disabledFalse disabled).elim)
    (fun disabled => (disabledFalse disabled).elim)
    (by simp only [b, armBody, earlyOutputCode, enabled, ite_true]; rfl)
    rfl (by simp only [b, armBody, decisionCode, enabled, ite_true]; rfl)
    (by simp only [b, armBody, fastOutputCode, enabled, ite_true]; rfl) rfl
    rfl rfl armSpecs_repair ⟨rfl,rfl⟩ rfl rfl rfl enabled
    memory left right output flag flagFit call

#print axioms arm_helper_checked_with_flag
end UInt256Proof.Add.Safety
