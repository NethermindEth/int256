import CIL.Safety.SymbolicExecution
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

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Checked execution from helper entry for the mathematical fast case. -/
theorem vector128_fast_entry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
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
  let value := vector128Saved body.profile.advSimd flag original left right
  apply vector128_dispatch_checked program body method specs found startCode incomingCode
    correctionCodeFound firstFourteen sse ssse earlyCode propCode decisionCodeFound original
    entered inputs outputs left right output frame slots args call setup layout homes leftMember
    rightMember outputMember leftArg rightArg outputArg flag flagFit flagArg post
  intro current _ _ _ snapshots earlyRead currentCall authority footprint _ _
  simp only [fast, ite_true]
  apply vector128_fast_suffix program body method specs found fastCode returns original entered
    current inputs outputs output (vector128SavedFrame frame slots right) _ slots rfl args call
    currentCall outputMember authority outputArg homes value
    (fun i lower => by
      obtain ⟨home, slot, loaded⟩ := snapshots ⟨i, by omega⟩
      exact ⟨home, slot, by
        simpa only [value, vector128Saved, show i < 13 by omega, ↓reduceDIte] using loaded⟩)
    earlyRead post
  intro after lowRead highRead afterCall outside
  have teardown := leaveFrame_preserves_memory_below (vector128SavedFrame frame slots right)
    after original.nextIdentity
    (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1)
  obtain ⟨allocation, present, _, _⟩ :=
    formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans lowRead
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans highRead
  obtain ⟨lowWords, highWords⟩ :=
    vector128_snapshot_fast_words original left right body.profile.advSimd flag fast
  rw [show value 9 = vector128SnapshotValue original left right 9 from rfl, lowWords] at lo
  rw [show value 10 = vector128SnapshotValue original left right 10 from rfl, highWords] at hi
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [output_value_of_packed_halves _ _ _ lo hi, UInt256Proof.sumWords_sum,
      input_limbs_value, input_limbs_value]
  · exact (teardown.access output old 32 1 true).trans
      (afterCall.1.writable (wordView output) (List.mem_map.mpr ⟨output, outputMember, rfl⟩))
  · intro id offset earlier untouched
    exact (teardown.cells id earlier offset).trans
      ((outside id offset untouched).trans (footprint id offset earlier untouched))

end UInt256Proof.Add.Safety
