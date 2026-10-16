import UInt256.Methods.Add.Vector128FastOutput
import UInt256.Methods.Add.Vector128FastArithmetic
import UInt256.Safety.HalfValue

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD

theorem vector128_snapshot_low (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 9 =
      correctedLo (inputLimb memory left) (inputLimb memory right) := by
  simp only [vector128SnapshotValue, show (9 : Fin 11).val = 9 from rfl]
  simpa only [input_half_low, input_half_high] using
    vector128_low_corrected (inputLimb memory left) (inputLimb memory right)

theorem vector128_snapshot_high (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 10 =
      correctedHi (inputLimb memory left) (inputLimb memory right) := by
  simp only [vector128SnapshotValue, show (10 : Fin 11).val = 10 from rfl]
  simpa only [input_half_low, input_half_high] using
    vector128_high_corrected (inputLimb memory left) (inputLimb memory right)

theorem vector128_snapshot_incoming_low (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 7 = pack128 (BitVec.ofNat 64 0)
      (carryMask (inputLimb memory left 0) (inputLimb memory right 0)) := by
  simp only [vector128SnapshotValue, show (7 : Fin 11).val = 7 from rfl]
  simp only [input_half_low, input_half_high, incoming128Low,
    halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]
  rfl

theorem vector128_snapshot_incoming_high (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 8 = pack128
      (carryMask (inputLimb memory left 1) (inputLimb memory right 1))
      (carryMask (inputLimb memory left 2) (inputLimb memory right 2)) := by
  simp only [vector128SnapshotValue, show (8 : Fin 11).val = 8 from rfl]
  simp only [input_half_low, input_half_high, incoming128High,
    halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]

theorem vector128_branch_low (memory : Memory) (left right : Reference) :
    vector128BranchValue memory left right 11 =
      propagationLo (inputLimb memory left) (inputLimb memory right) := by
  change propagating128 (vector128SnapshotValue memory left right 9)
    (vector128SnapshotValue memory left right 7) = _
  rw [vector128_snapshot_low, vector128_snapshot_incoming_low]
  exact vector128_low_propagation _ _

theorem vector128_branch_high (memory : Memory) (left right : Reference) :
    vector128BranchValue memory left right 12 =
      propagationHi (inputLimb memory left) (inputLimb memory right) := by
  change propagating128 (vector128SnapshotValue memory left right 10)
    (vector128SnapshotValue memory left right 8) = _
  rw [vector128_snapshot_high, vector128_snapshot_incoming_high]
  exact vector128_high_propagation _ _

/-- The actual saved fast condition implies the saved output halves encode the sum of the initial caller operands, including overlapping views. -/
theorem vector128_snapshot_fast_words (memory : Memory) (left right : Reference) (advSimd : Bool) (flag : BitVec 32)
    (fast : selectedPropagation128 advSimd flag (vector128BranchValue memory left right 11)
      (vector128BranchValue memory left right 12) = BitVec.ofNat 128 0) :
    let words := sumWords (inputLimb memory left) (inputLimb memory right)
    vector128SnapshotValue memory left right 9 = pack128 (words 0) (words 1) ∧
    vector128SnapshotValue memory left right 10 = pack128 (words 2) (words 3) := by
  rw [vector128_branch_low, vector128_branch_high] at fast
  simpa only [vector128_snapshot_low, vector128_snapshot_high] using
    vector128_fast_words advSimd (inputLimb memory left) (inputLimb memory right) flag fast

#print axioms vector128_snapshot_fast_words
#print axioms vector128_snapshot_low
#print axioms vector128_snapshot_high
#print axioms vector128_snapshot_incoming_low
#print axioms vector128_snapshot_incoming_high
#print axioms vector128_branch_low
#print axioms vector128_branch_high
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete checked fast suffix, with initialized output halves and the exact saved high-mask flag. -/
theorem vector128_fast_suffix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 204)
    (code : body.code = leading ++ fastOutputCode body.profile.advSimd ++ tail)
    (returns : body.returnsValue = true) (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[10]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (earlyRead : body.profile.advSimd = true →
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
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      current.nextIdentity ≤ after.nextIdentity →
      post (leaveFrame frame after)
        [.scalar (.i32 (if CIL.Vector.lane64 carry 1 > BitVec.ofNat 64 0 then 1 else 0))]) :
    ∃ fuel result returned,
      run program fuel method 204 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_fast_output_dispatch program body method found leading tail leadingLength code current frame args post
  apply vector128_fast_output program body method found leading tail leadingLength code original entered current inputs outputs output frame args
    call currentCall member authority argument low high lowHome highHome lowSlot highSlot
    highBound lowRead highRead earlyRead post
  intro after outputRead afterCall afterAuthority outside privateReads advanced
  exact ⟨7, _, _, vector128_fast_return program body method found leading tail leadingLength code returns after frame args carryHome carry carrySlot
    (privateReads carryHome 16 1 _ carryBound carryRead),
    continuation after outputRead afterCall afterAuthority outside advanced⟩

#print axioms vector128_fast_suffix
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete fast suffix with initial-input arithmetic and surviving caller memory guarantees. -/
theorem vector128_fast_result (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 204)
    (code : body.code = leading ++ fastOutputCode body.profile.advSimd ++ tail)
    (returns : body.returnsValue = true) (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[10]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (earlyRead : body.profile.advSimd = true →
      read current output 16 1 = .ok (numberBytes low.toNat 16) ∧
      read current { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16))
    (carryHome : Reference) (carry : BitVec 128)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryBound : original.nextIdentity ≤ carryHome.allocation)
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (left right : Reference) (flag : BitVec 32)
    (lowValue : low = vector128SnapshotValue original left right 9)
    (highValue : high = vector128SnapshotValue original left right 10)
    (fast : selectedPropagation128 body.profile.advSimd flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) = BitVec.ofNat 128 0)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 204 args frame [] current = .ok (final, returned) ∧
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
  apply vector128_fast_suffix program body method found leading tail leadingLength code returns original entered current inputs outputs output frame args
    call currentCall member authority argument low high lowHome highHome lowSlot highSlot
    highBound lowRead highRead earlyRead carryHome carry carrySlot carryBound carryRead post
  intro after outputRead afterCall afterAuthority outside advanced
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans outputRead.1
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans outputRead.2
  obtain ⟨lowWords, highWords⟩ := vector128_snapshot_fast_words original left right body.profile.advSimd flag fast
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

/-- Checked execution from helper entry for the mathematical fast case. -/
theorem vector128_fast_entry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = vector128AddPrefix ++ startTail)
    (incomingCode : body.code = incomingPrefix body.profile.advSimd ++ incomingTail)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)     (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)     (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail)     (decisionLeading decisionTail : List CIL.Op) (decisionLength : decisionLeading.length = 94)
    (decisionCodeFound : body.code = decisionLeading ++ decisionCode body.profile.advSimd ++ decisionTail)     (fastLeading fastTail : List CIL.Op) (fastLength : fastLeading.length = 204)
    (fastCode : body.code = fastLeading ++ fastOutputCode body.profile.advSimd ++ fastTail)
    (returns : body.returnsValue = true) (original entered : Memory)
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
    (fast : selectedPropagation128 body.profile.advSimd flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) = BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
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
  apply vector128_dispatch_checked program body method specs found startTail incomingTail leading correctionTail startCode incomingCode leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound original entered inputs outputs left right output frame slots args
    call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagFit flagArg post
  intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced _callerPreserved
  simp only [fast, ite_true]
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  obtain ⟨carryHome, carrySlot, carryRead⟩ := snapshots 6
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
    vector128_fast_result program body method found fastLeading fastTail fastLength fastCode returns original entered current inputs outputs output
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
