import UInt256.Methods.Add.Vector128ARMRepairRun
import UInt256.Methods.Add.Vector128FastEntry

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Both ARM helper branches from entry: independent modular addition,
    normal checked return and surviving caller memory guarantees. -/
theorem vector128_arm_entry (enabled : Extracted.profile.advSimd = true) (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vector128Body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    : ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered = .ok (final, returned) ∧
      (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧
        (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
          if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  by_cases fast : selectedPropagation128 flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) = BitVec.ofNat 128 0
  · obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
      vector128_fast_entry original entered inputs outputs left right output frame slots args
        call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagArg fast
    exact ⟨fuel, final, returned, executed, ⟨_, scalar, fun reporting => vector128_snapshot_fast_flag original left right flag reporting fast⟩,
      result, writable, outside⟩
  · let post : Memory → List Value → Prop := fun final returned =>
      (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧
        (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
          if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset)
    apply vector128_dispatch_checked original entered inputs outputs left right output frame slots args
      call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagArg post
    intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced _callerPreserved
    simp only [fast, ite_false]
    apply vector128_repair_dispatch current (vector128SavedFrame frame slots right) args post
    simp only [vector128RepairStart, enabled, ite_true]
    have extended : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read current reference 16 1 = .ok (numberBytes (vector128DecisionValues original left right flag i).toNat 16) := by
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
      vector128_arm_repair_run enabled original entered current inputs outputs left right output
        (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args
        call currentCall (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
        outputMember outputArg flag flagArg extended (earlyRead enabled).1
        (fun id member => (fresh.2 id member).1)
    exact ⟨fuel, final, returned, executed, ⟨_, scalar, fun _ => rfl⟩, result, writable,
      fun id offset bound untouched => (outside id offset bound untouched).trans (footprint id offset bound untouched)⟩

#print axioms vector128_arm_entry
end UInt256Proof.Add.Safety
