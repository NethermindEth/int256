import UInt256.Methods.Add.Vector128Dispatch
import UInt256.Methods.Add.Vector128FastResult

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Checked execution from helper entry for the mathematical fast case.
    The complementary repair case remains a separate proof obligation. -/
theorem vector128_fast_entry (original entered : Memory)
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
    (fast : selectedPropagation128 flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) = BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered = .ok (final, returned) ∧
      returned = [.scalar (.i32 (if CIL.Vector.lane64 (vector128SnapshotValue original left right 6) 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if CIL.Vector.lane64 (vector128SnapshotValue original left right 6) 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
    inputValue final output = inputValue original left + inputValue original right ∧
    access final output 32 1 true = .ok () ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = original.cells id offset)
  apply vector128_dispatch_checked original entered inputs outputs left right output frame slots args
    call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagArg post
  intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced _callerPreserved
  simp only [fast, ite_true]
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  obtain ⟨carryHome, carrySlot, carryRead⟩ := snapshots 6
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
    vector128_fast_result original entered current inputs outputs output
      (vector128SavedFrame frame slots right) args call currentCall outputMember authority outputArg
      (vector128SnapshotValue original left right 9) (vector128SnapshotValue original left right 10)
      lowHome highHome lowSlot highSlot (homes.home_bound 10 .vector128 highHome highSlot)
      lowRead highRead earlyRead carryHome (vector128BranchValue original left right 6) carrySlot
      (homes.home_bound 6 .vector128 carryHome carrySlot) carryRead left right flag rfl rfl fast
      (fun id member => (fresh.2 id member).1)
  exact ⟨fuel, final, returned, executed, scalar, result, writable,
    fun id offset old untouched => (outside id offset old untouched).trans (footprint id offset old untouched)⟩

#print axioms vector128_fast_entry
end UInt256Proof.Add.Safety
