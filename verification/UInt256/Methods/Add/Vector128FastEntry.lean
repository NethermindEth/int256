import UInt256.Methods.Add.Vector128FastOutput
import UInt256.Methods.Add.Vector128SnapshotArithmetic
import UInt256.Safety.HalfOutputValue
import CIL.Safety.ReturnMemory
import UInt256.Methods.Add.Vector128Dispatch

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete checked fast suffix, with initialized output halves and the exact
    saved high-mask flag. Arithmetic interpretation is supplied by the caller. -/
theorem vector128_fast_suffix (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[10]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (earlyRead : Extracted.profile.advSimd = true →
      read current output 16 1 = .ok (numberBytes low.toNat 16) ∧
      read current { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16))
    (carryHome : Reference) (carry : BitVec 128)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryBound : original.nextIdentity ≤ carryHome.allocation)
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      current.nextIdentity ≤ after.nextIdentity →
      post (leaveFrame frame after)
        [.scalar (.i32 (if CIL.Vector.lane64 carry 1 > BitVec.ofNat 64 0 then 1 else 0))]) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 204 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_fast_output_dispatch current frame args post
  apply vector128_fast_output original entered current inputs outputs output frame args
    call currentCall member authority argument low high lowHome highHome lowSlot highSlot
    highBound lowRead highRead earlyRead post
  intro after outputRead afterCall afterAuthority outside privateReads advanced
  exact ⟨7, _, _, vector128_fast_return after frame args carryHome carry carrySlot
    (privateReads carryHome 16 1 _ carryBound carryRead),
    continuation after outputRead afterCall afterAuthority outside advanced⟩

#print axioms vector128_fast_suffix
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete fast suffix with initial-input arithmetic and surviving caller
    memory guarantees. Private-frame freshness is supplied by actual setup. -/
theorem vector128_fast_result (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[10]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (earlyRead : Extracted.profile.advSimd = true →
      read current output 16 1 = .ok (numberBytes low.toNat 16) ∧
      read current { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16))
    (carryHome : Reference) (carry : BitVec 128)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryBound : original.nextIdentity ≤ carryHome.allocation)
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (left right : Reference) (flag : BitVec 32)
    (lowValue : low = vector128SnapshotValue original left right 9)
    (highValue : high = vector128SnapshotValue original left right 10)
    (fast : selectedPropagation128 flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) = BitVec.ofNat 128 0)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 204 args frame [] current = .ok (final, returned) ∧
      returned = [.scalar (.i32 (if CIL.Vector.lane64 carry 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if CIL.Vector.lane64 carry 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
    inputValue final output = inputValue original left + inputValue original right ∧
    access final output 32 1 true = .ok () ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset)
  apply vector128_fast_suffix original entered current inputs outputs output frame args
    call currentCall member authority argument low high lowHome highHome lowSlot highSlot
    highBound lowRead highRead earlyRead carryHome carry carrySlot carryBound carryRead post
  intro after outputRead afterCall afterAuthority outside advanced
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans outputRead.1
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans outputRead.2
  obtain ⟨lowWords, highWords⟩ := vector128_snapshot_fast_words original left right flag fast
  rw [lowValue, lowWords] at lo
  rw [highValue, highWords] at hi
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [output_value_of_packed_halves _ _ _ lo hi, UInt256Proof.sumWords_sum,
      input_limbs_value, input_limbs_value]
  · exact (teardown.access output old 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  · intro id offset earlier untouched
    exact (teardown.cells id earlier offset).trans (outside id offset untouched)

#print axioms vector128_fast_result
end UInt256Proof.Add.Safety

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
