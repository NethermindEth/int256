import UInt256.Methods.Add.SSERepair
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
def sseBody (profile : CIL.FeatureProfile) (carry storage : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .v128 0, .v128 0, .v128 0, .v128 0], localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .word64, .word64, .word64, .word64, .word64, .vector128, .vector128, .vector128, .vector128], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .memory .asRef,
  .memory .asRef,
  .arg 1,
  .memory .asRef,
  .memory .asRef,
  .setLocal 0,
  .dup,
  .memory .load128,
  .setLocal 1,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 2,
  .local 0,
  .memory .load128,
  .setLocal 3,
  .local 0,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 4,
  .local 1,
  .local 3,
  .intrinsic (.vector (.add64 128)) 2,
  .local 2,
  .local 4,
  .intrinsic (.vector (.add64 128)) 2,
  .setLocal 5,
  .dup,
  .local 1,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 6,
  .local 5,
  .local 2,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 7,
  .feature .advSimd,
  .brzero 50,
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
  .local 6,
  .const32 8,
  .intrinsic (.sse .shiftLeftBytes) 2,
  .setLocal 8,
  .local 7,
  .intrinsic (.vector (.reinterpret 128)) 1,
  .local 6,
  .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8,
  .intrinsic (.sse .alignBytes) 3,
  .intrinsic (.vector (.reinterpret 128)) 1,
  .setLocal 9,
  .local 8,
  .intrinsic (.vector (.sub64 128)) 2,
  .setLocal 10,
  .local 5,
  .local 9,
  .intrinsic (.vector (.sub64 128)) 2,
  .setLocal 11,
  .arg 2,
  .skipInit,
  .feature .advSimd,
  .brzero 82,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 10,
  .intrinsic (.vector (.zero 128)) 0,
  .intrinsic (.vector (.eq64 128)) 2,
  .local 8,
  .intrinsic (.vector (.band 128)) 2,
  .setLocal 12,
  .local 11,
  .intrinsic (.vector (.zero 128)) 0,
  .intrinsic (.vector (.eq64 128)) 2,
  .local 9,
  .intrinsic (.vector (.band 128)) 2,
  .setLocal 13,
  .feature .advSimd,
  .brzero 98,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 12,
  .local 13,
  .intrinsic (.vector (.bor 128)) 2,
  .branch 106,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .setLocal 14,
  .local 14,
  .intrinsic (.vector (.zero 128)) 0,
  .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero 204,
  .feature .advSimd,
  .brzero 162,
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
  .const32 0,
  .convI8,
  .setLocal 15,
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .fieldAt 0 8,
  .localAddr 15,
  .localAddr 16,
  .call carry 4,
  .arg 0,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 8 8,
  .localAddr 15,
  .localAddr 17,
  .call carry 4,
  .arg 0,
  .fieldAt 16 8,
  .arg 1,
  .fieldAt 16 8,
  .localAddr 15,
  .localAddr 18,
  .call carry 4,
  .arg 0,
  .fieldAt 24 8,
  .arg 1,
  .fieldAt 24 8,
  .localAddr 15,
  .localAddr 19,
  .call carry 4,
  .arg 2,
  .local 16,
  .local 17,
  .local 18,
  .local 19,
  .call storage 5,
  .local 15,
  .const32 0,
  .convI8,
  .gtu,
  .ret (some .unsigned8),
  .feature .advSimd,
  .brnonzero 215,
  .arg 2,
  .memory .asRef,
  .dup,
  .local 10,
  .memory .store128,
  .const32 1,
  .memory (.add 16 true),
  .local 11,
  .memory .store128,
  .local 7,
  .const32 1,
  .intrinsic (.vector (.extract64 128)) 2,
  .const32 0,
  .convI8,
  .gtu,
  .ret (some .unsigned8)] }
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.CarrySafety

/-- Both SSE helper branches from entry: modular sum of the initial operands, checked return and caller bytes kept. -/
theorem vector128_sse_entry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = vector128AddPrefix ++ startTail)
    (incomingCode : body.code = incomingPrefix body.profile.advSimd ++ incomingTail)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)
    (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail)
    (decisionLeading decisionTail : List CIL.Op) (decisionLength : decisionLeading.length = 94)
    (decisionCodeFound : body.code = decisionLeading ++ decisionCode body.profile.advSimd ++ decisionTail)
    (fastLeading fastTail : List CIL.Op) (fastLength : fastLeading.length = 204)
    (fastCode : body.code = fastLeading ++ fastOutputCode body.profile.advSimd ++ fastTail)
    (returns : body.returnsValue = true)
    (repairDispatchLeading repairDispatchTail : List CIL.Op) (repairDispatchLength : repairDispatchLeading.length = 111)
    (repairDispatchCode : body.code = repairDispatchLeading ++ [.feature .advSimd, .brzero 162] ++ repairDispatchTail)
    (repairLeading repairTail : List CIL.Op) (repairLength : repairLeading.length = 162)
    (carry storage : Nat) (repairCode : body.code = repairLeading ++ sseRepairCode carry storage ++ repairTail)
    (carryFound : program[carry]? = some (carryBody body.profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (wordSpecs : ∀ i : Fin 5, specs[14 + i.val]? = some armWordSpec)
    (disabled : body.profile.advSimd = false) (original entered : Memory)
    (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
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
      vector128_fast_entry program body method specs found startTail incomingTail leading correctionTail startCode incomingCode leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound fastLeading fastTail fastLength fastCode returns original entered [left, right] [output] left right output frame slots args
        call setup layout homes (by simp) (by simp) (by simp) leftArg rightArg outputArg flag flagFit flagArg fast
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
    apply vector128_dispatch_checked program body method specs found startTail incomingTail leading correctionTail startCode incomingCode leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound original entered [left, right] [output] left right output frame slots args
      call setup layout homes (by simp) (by simp) (by simp) leftArg rightArg outputArg flag flagFit flagArg post
    intro current _conditionHome _conditionSlot _conditionRead _snapshots _earlyRead currentCall authority _footprint _advanced callerPreserved
    simp only [fast, ite_false]
    apply vector128_repair_dispatch program body method found repairDispatchLeading repairDispatchTail repairDispatchLength repairDispatchCode current (vector128SavedFrame frame slots right) args post
    simp only [vector128RepairStart, disabled, Bool.false_eq_true, ite_false]
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    apply vector128_sse_repair_carry program body method specs found repairLeading repairTail repairLength carry storage repairCode carryFound wordSpecs
      original entered current (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl left right output
      call currentCall (callerPreserved disabled) homes (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) authority
      args leftArg rightArg post
    intro carryHome results after state
    obtain ⟨fuel, final, values, executed, result⟩ := vector128_sse_finish program body method found repairLeading repairTail repairLength
      carry storage repairCode storageFound returns original after (vector128SavedFrame frame slots right)
      left right output carryHome results args outputArg call (fun id member => (fresh.2 id member).1) state
    exact ⟨fuel, final, values, executed, ⟨_, result.flag, (by unfold UInt256Proof.Safety.addOverflow; split <;> rfl), fun _ => rfl⟩, result.value, result.writable,
      fun id offset bound untouched => result.footprint id bound offset untouched⟩

#print axioms vector128_sse_entry
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.CarrySafety

/-- Checked invocation of an SSE helper body. -/
theorem checked_vector128_sse_contract (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = vector128AddPrefix ++ startTail)
    (incomingCode : body.code = incomingPrefix body.profile.advSimd ++ incomingTail)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)
    (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail)
    (decisionLeading decisionTail : List CIL.Op) (decisionLength : decisionLeading.length = 94)
    (decisionCodeFound : body.code = decisionLeading ++ decisionCode body.profile.advSimd ++ decisionTail)
    (fastLeading fastTail : List CIL.Op) (fastLength : fastLeading.length = 204)
    (fastCode : body.code = fastLeading ++ fastOutputCode body.profile.advSimd ++ fastTail)
    (returns : body.returnsValue = true)
    (repairDispatchLeading repairDispatchTail : List CIL.Op) (repairDispatchLength : repairDispatchLeading.length = 111)
    (repairDispatchCode : body.code = repairDispatchLeading ++ [.feature .advSimd, .brzero 162] ++ repairDispatchTail)
    (repairLeading repairTail : List CIL.Op) (repairLength : repairLeading.length = 162)
    (carry storage : Nat) (repairCode : body.code = repairLeading ++ sseRepairCode carry storage ++ repairTail)
    (carryFound : program[carry]? = some (carryBody body.profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (wordSpecs : ∀ i : Fin 5, specs[14 + i.val]? = some armWordSpec)
    (metadata : body.localKinds = .reference :: specs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: specs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (opaqueLocals : body.opaqueVectorLocals = []) (disabled : body.profile.advSimd = false)
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
    vector128_sse_entry program body method specs found startTail incomingTail leading correctionTail startCode incomingCode leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound fastLeading fastTail fastLength fastCode returns repairDispatchLeading repairDispatchTail repairDispatchLength repairDispatchCode repairLeading repairTail repairLength carry storage repairCode carryFound storageFound wordSpecs disabled memory entered left right output frame slots args
      call setup layout homes rfl rfl rfl flag flagFit rfl
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

#print axioms checked_vector128_sse_contract
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.CarrySafety

theorem armSpecs_words : ∀ i : Fin 5, armSpecs[14 + i.val]? = some armWordSpec := by
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The extracted SSE AddVector128 body with its carry and storage callees. -/
theorem sse_helper_checked (profile : CIL.FeatureProfile) (disabled : profile.advSimd = false)
    (sse2 : profile.sse2 = true) (ssse3 : profile.ssse3 = true)
    (program : CIL.Program) (method carry storage : Nat) (found : program[method]? = some (sseBody profile carry storage))
    (carryFound : program[carry]? = some (carryBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
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
  let b := sseBody profile carry storage
  apply checked_vector128_sse_contract program b method armSpecs found
    (b.code.drop 37) (b.code.drop 62) (b.code.take 62) (b.code.drop 69)
    rfl (by simp only [b, sseBody, incomingPrefix, disabled, Bool.false_eq_true, ite_false]; rfl)
    rfl rfl armSpecs_first (fun _ => sse2) (fun _ => ssse3)
    (b.code.take 69) (b.code.drop 82) rfl (by simp only [b, sseBody, earlyOutputCode, disabled, Bool.false_eq_true, ite_false]; rfl)
    (b.code.take 82) (b.code.drop 94) rfl rfl
    (b.code.take 94) (b.code.drop 111) rfl (by simp only [b, sseBody, decisionCode, disabled, Bool.false_eq_true, ite_false]; rfl)
    (b.code.take 204) (b.code.drop 222) rfl (by simp only [b, sseBody, fastOutputCode, disabled, Bool.false_eq_true, ite_false]; rfl) rfl
    (b.code.take 111) (b.code.drop 113) rfl rfl
    (b.code.take 162) (b.code.drop 204) rfl carry storage rfl carryFound storageFound armSpecs_words
    ⟨rfl, rfl⟩ rfl rfl rfl disabled
    memory left right output flag flagFit call

#print axioms armSpecs_words
#print axioms sse_helper_checked
end UInt256Proof.Add.Safety
