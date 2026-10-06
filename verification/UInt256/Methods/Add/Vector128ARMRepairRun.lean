import UInt256.Methods.Add.Vector128ARMRepairState
import UInt256.Methods.Add.Vector128ARMRepairResult
import UInt256.Methods.Add.Vector128ReportingArithmetic

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete ARM repair branch from saved initial-input snapshots to normal
    return, retaining the independent sum and caller memory guarantees. -/
theorem vector128_arm_repair_run (enabled : Extracted.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (left right output : Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current) (member : output ∈ outputs)
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (vector128DecisionValues original left right flag i).toNat 16))
    (lowRead : read current output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16))
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 113 args frame [] current = .ok (final, returned) ∧
      returned = [.scalar (.i32 (if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0))] ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0))] ∧
    inputValue final output = inputValue original left + inputValue original right ∧
    access final output 32 1 true = .ok () ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset)
  apply vector128_arm_repair_checked enabled original.nextIdentity entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority flag flagArg (vector128DecisionValues original left right flag) rfl snapshots post
  intro after repaired preserved afterCall afterAuthority advanced
  obtain ⟨carryHome, carrySlot, carryRead⟩ := repaired 6
  obtain ⟨highHome, highSlot, highRead⟩ := repaired 10
  change slots[6]? = _ at carrySlot
  change slots[10]? = _ at highSlot
  have actualCarry : frame.locals[7]? = some (.bytes .vector128 carryHome) := by simpa [layout] using carrySlot
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have savedLow := (preserved.read output old 16 1).trans lowRead
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
    vector128_arm_repair_result enabled original entered after inputs outputs output frame args
      call afterCall member afterAuthority outputArg (vector128SnapshotValue original left right 9)
      (armRepairSnapshot (vector128DecisionValues original left right flag) 10)
      highHome actualHigh highRead savedLow carryHome
      (armRepairSnapshot (vector128DecisionValues original left right flag) 6) actualCarry
      (homes.home_bound 6 .vector128 carryHome carrySlot) carryRead left right
      (vector128_snapshot_low original left right) (vector128_repaired_snapshot_high original left right flag) owned
  rw [vector128_snapshot_repaired_flag] at scalar
  exact ⟨fuel, final, returned, executed, scalar, result, writable,
    fun id offset bound untouched => (outside id offset bound untouched).trans (preserved.cells id bound offset)⟩

#print axioms vector128_arm_repair_run
end UInt256Proof.Add.Safety
