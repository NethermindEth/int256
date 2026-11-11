import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.Vector128Propagation

/-!
Vector128 addition's fast/repair decision: store the propagation condition the selected ISA
and reporting mode test, branch on it, and compose the helper from entry to that branch.
-/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def decisionCode (adv : Bool) : List CIL.Op := if adv then [
  .feature .advSimd, .brzero 98,
  .arg 3 (some .unsigned8), .brzero 102,
  .local 12, .local 13, .intrinsic (.vector (.bor 128)) 2, .branch 106,
  .local 12, .local 13, .const32 1, .intrinsic (.advSimd .extract64) 3,
  .setLocal 14,
  .local 14, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero 204
] else [
  .feature .advSimd, .brzero 98,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 12, .local 13, .intrinsic (.vector (.bor 128)) 2, .branch 106,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .setLocal 14,
  .local 14, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero 204]

/-- Store the propagation condition of the selected ISA and reporting mode, then branch on
    it to the fast suffix or the repair. -/
theorem vector128_decision_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 94 (decisionCode body.profile.advSimd))
    (slotSpec : specs[13]? = some vector128ZeroSpec)
    (boundary : Nat) (origin entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (argument : args[3]? = some (.scalar (.i32 flag))) (value : Nat → BitVec 128)
    (condition : value 13 =
      selectedPropagation128 body.profile.advSimd flag (value 11) (value 12))
    (state : VectorState program boundary origin entered current inputs outputs slots value 13)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program boundary origin entered after inputs outputs slots value 14 →
      ∃ fuel result returned,
        run program fuel method (if value 13 = BitVec.ofNat 128 0 then 204 else 111) args frame
          [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 94 args frame [] current = .ok (result, returned) ∧
        post result returned := by
  have tail : CodeAt body 107 [.local 14, .intrinsic (.vector (.zero 128)) 0,
      .intrinsic (.vector (.equalsAll 128)) 2, .brnonzero 204] := by
    cases selected : body.profile.advSimd <;> simp only [selected] at code <;> exact code.drop 13
  have branch : ∀ after,
      VectorState program boundary origin entered after inputs outputs slots value 14 →
      ∃ fuel result returned,
        run program fuel method 107 args frame [] after = .ok (result, returned) ∧
          post result returned := by
    intro after saved
    have reload := saved.snapshots.load frame root layout 13 (by decide) body
    have done := continuation after saved
    cil_contract_steps 3 [found, tail, reload, intrinsic_zero128, intrinsic_equal_all128]
    change ∃ fuel result returned, run program fuel method 110 args frame [.scalar (.i32
      (if value 13 == BitVec.ofNat 128 0 then 1 else 0))] after = _ ∧ _
    by_cases zero : value 13 = BitVec.ofNat 128 0
    all_goals
      simp only [beq_iff_eq, zero, ↓reduceIte] at done ⊢
      cil_contract_steps [found, tail] until done
  have loadLow := state.snapshots.load frame root layout 11 (by decide) body
  have loadHigh := state.snapshots.load frame root layout 12 (by decide) body
  cases selected : body.profile.advSimd <;> simp only [selected] at code condition
  · obtain ⟨after, saved, stored⟩ := state.store body specs frame root layout enteredWF homes
      slotSpec (value 11 ||| value 12) (by simp [condition, selectedPropagation128])
    cil_contract_steps [found, code, loadLow, loadHigh, stored, intrinsic_or128,
      show body.profile.evaluate .advSimd = false from selected] until branch after saved
  · have feature : body.profile.evaluate .advSimd = true := selected
    by_cases reporting : flag = BitVec.ofNat 32 0
    · subst reporting
      obtain ⟨after, saved, stored⟩ := state.store body specs frame root layout enteredWF homes
        slotSpec (advExtract64 (value 11) (value 12) 1)
        (by simp [condition, selectedPropagation128, incoming128_arm_high])
      cil_contract_steps [found, code, feature, selected, argument, flagFit, loadLow, loadHigh,
        stored, intrinsic_adv_extract] until branch after saved
    · obtain ⟨after, saved, stored⟩ := state.store body specs frame root layout enteredWF homes
        slotSpec (value 11 ||| value 12) (by simp [condition, selectedPropagation128, reporting])
      cil_contract_steps [found, code, feature, argument, flagFit, reporting, loadLow, loadHigh,
        stored, intrinsic_or128] until branch after saved

/-- The fourteen private vectors saved by the decision: the thirteen before it and the
    condition it tests. -/
def vector128Saved (advSimd : Bool) (flag : BitVec 32) (memory : Memory) (left right : Reference)
    (i : Nat) : BitVec 128 :=
  if within : i < 13 then vector128BranchValue memory left right ⟨i, within⟩
  else selectedPropagation128 advSimd flag (vector128BranchValue memory left right 11)
    (vector128BranchValue memory left right 12)
/-- Complete checked helper prefix through the actual fast/repair branch, preserving all saved values and any early ARM output writes. -/
theorem vector128_dispatch_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startCode : CodeAt body 0 vector128AddPrefix)
    (incomingCode : CodeAt body 0 (incomingPrefix body.profile.advSimd))
    (correctionCodeFound : CodeAt body 62 correctionCode)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (earlyCode : CodeAt body 69 (earlyOutputCode body.profile.advSimd))
    (propCode : CodeAt body 82 (propagationCode))
    (decisionCodeFound : CodeAt body 94 (decisionCode body.profile.advSimd)) (original entered : Memory)
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
    (post : Memory → List Value → Prop)
    (continuation : ∀ after conditionHome,
      slots[13]? = some (.bytes .vector128 conditionHome) →
      read after conditionHome 16 1 = .ok (numberBytes
        (selectedPropagation128 body.profile.advSimd flag (vector128BranchValue original left right 11)
          (vector128BranchValue original left right 12)).toNat 16) →
      (∀ i : Fin 13, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16)) →
      (body.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) →
      entered.nextIdentity ≤ after.nextIdentity →
      (body.profile.advSimd = false → MemoryBelow original.nextIdentity original after) →
      ∃ fuel result returned,
        run program fuel method
          (if selectedPropagation128 body.profile.advSimd flag (vector128BranchValue original left right 11)
            (vector128BranchValue original left right 12) = BitVec.ofNat 128 0 then 204 else 111) args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  let value := vector128Saved body.profile.advSimd flag original left right
  let saved := vector128SavedFrame frame slots right
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply vector128_inputs_checked program body method specs found (startCode.take 22)
    (fun i => firstFourteen ⟨i.val, by omega⟩) original entered inputs outputs left right frame
    slots args call setup layout homes leftMember rightMember leftArg rightArg value rfl rfl rfl
    rfl post
  intro inputsSaved inputsState
  apply vector128_sum_checked program body method specs found startCode
    (fun i => firstFourteen ⟨i.val, by omega⟩) original.nextIdentity original entered inputsSaved
    inputs outputs saved _ slots rfl args enteredWF homes value rfl rfl rfl inputsState post
  intro summed sumState
  apply vector128_incoming_checked program body method specs found 37 5
    (incomingPrefix_block incomingCode) sse ssse (firstFourteen 7) (firstFourteen 8)
    original.nextIdentity original entered summed inputs outputs saved _ slots rfl args _
    enteredWF homes value rfl rfl sumState post
  intro shifted incomingState
  apply vector128_correction_checked program body method specs found correctionCodeFound
    (firstFourteen 9) (firstFourteen 10) original.nextIdentity original entered shifted inputs
    outputs saved _ slots rfl args enteredWF homes value _ rfl rfl incomingState post
  intro corrected resultState
  apply vector128_early_output program body method specs found earlyCode original entered
    corrected inputs outputs output saved _ slots rfl args call outputMember outputArg homes
    value resultState post
  intro early earlyState outputRead footprint callerPreserved
  apply vector128_propagation_checked program body method specs found propCode
    (firstFourteen 11) (firstFourteen 12) original.nextIdentity early entered early inputs
    outputs saved _ slots rfl args enteredWF homes value rfl rfl earlyState post
  intro propagated maskState
  apply vector128_decision_checked program body method specs found decisionCodeFound
    (firstFourteen 13) original.nextIdentity early entered propagated inputs outputs saved _
    slots rfl args enteredWF homes flag flagFit flagArg value rfl maskState post
  intro after state
  obtain ⟨conditionHome, conditionSlot, conditionRead⟩ := state.snapshots 13 (by decide)
  obtain ⟨allocation, present, _, _⟩ :=
    formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  exact continuation after conditionHome conditionSlot conditionRead
    (fun i => by
      obtain ⟨home, slot, loaded⟩ := state.snapshots i.val (by omega)
      exact ⟨home, slot, by simpa only [value, vector128Saved, i.isLt, ↓reduceDIte] using loaded⟩)
    (fun enabled => ⟨(state.preserved.read output old 16 1).trans (outputRead enabled).1,
      (state.preserved.read { output with offset := output.offset + 16 } old 16 1).trans
        (outputRead enabled).2⟩)
    state.call state.authority
    (fun id offset bound outside =>
      (state.preserved.cells id bound offset).trans (footprint id offset bound outside))
    state.advanced (fun disabled => (callerPreserved disabled).trans state.preserved)

end UInt256Proof.Add.Safety
