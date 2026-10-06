import UInt256.Methods.Add.Vector128ARMRepairCarry
import UInt256.Methods.Add.Vector128SnapshotArithmetic
import UInt256.Safety.HalfOutputValue
import CIL.Safety.ReturnMemory
import UInt256.Methods.Add.Vector128ARMRepairState
import UInt256.Methods.Add.Vector128ReportingArithmetic

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The ARM repair suffix returns the updated high-lane carry bit and retires its frame.
    The arithmetic meaning of this flag is established separately from stepping. -/
theorem vector128_arm_repair_return (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (mask : BitVec 128)
    (slot : frame.locals[7]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes mask.toNat 16)) :
    run Extracted.program 7 vector128Index 155 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if CIL.Vector.lane64 mask 1 > BitVec.ofNat 64 0 then 1 else 0))]) := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 mask) mask.toNat rfl slot loaded
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    have profile : vector128Body.profile = Extracted.profile := by rfl
    have returns : vector128Body.returnsValue = true := by rfl
    iterate 6
      apply Eq.trans
      · apply run_next found (by rfl)
        first
        | exact load _ _
        | (simp (config := { implicitDefEqProofs := false })
            [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.binary,
              CIL.Intrinsic.available, CIL.Vector.intrinsic_extract128,
              checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
    have fetched : vector128Body.code[161]? = some .ret := by rfl
    simp [run, found, fetched, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_arm_repair_return
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Replace only the high output half, preserving the initialized low half and
    every private snapshot even when the original caller views overlap. -/
theorem vector128_arm_repair_output (enabled : Extracted.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (highHome : Reference)
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowRead : read current output 16 1 = .ok (numberBytes low.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 155 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 149 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨after, written, highOutput, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
      output_half_update Extracted.program original entered current inputs outputs output 1 high
        call currentCall member authority
    simp only [Fin.val_one, Nat.mul_one] at written highOutput
    have lowOutput := write_preserves_disjoint_read written lowRead (Or.inr (Or.inl (by simp)))
    have done := continuation after ⟨lowOutput, highOutput⟩ afterCall afterAuthority outside privateReads advanced
    have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 high) high.toNat rfl highSlot highRead
    have formed := currentCall.output_formed member
    have address := currentCall.output_half_address member 1
    simp only [Fin.val_one, Nat.mul_one] at address
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact loadHigh _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
               storeValue, referenceAt, written, address, CIL.offsetValue,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_repair_output
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete repaired output/return suffix. The saved carry mask survives the
    output write, and the continuation receives both initialized output halves. -/
theorem vector128_arm_repair_suffix (enabled : Extracted.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (highHome : Reference)
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowRead : read current output 16 1 = .ok (numberBytes low.toNat 16))
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
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 149 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_arm_repair_output enabled original entered current inputs outputs output frame args
    call currentCall member authority argument low high highHome highSlot highRead lowRead post
  intro after outputRead afterCall afterAuthority outside privateReads advanced
  exact ⟨7, _, _, vector128_arm_repair_return enabled after frame args carryHome carry carrySlot
    (privateReads carryHome 16 1 _ carryBound carryRead),
    continuation after outputRead afterCall afterAuthority outside advanced⟩

#print axioms vector128_arm_repair_suffix
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Repaired output halves encode the independent initial-input sum, and
    caller value/access/footprint guarantees survive the private frame return. -/
theorem vector128_arm_repair_result (enabled : Extracted.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (highHome : Reference)
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowRead : read current output 16 1 = .ok (numberBytes low.toNat 16))
    (carryHome : Reference) (carry : BitVec 128)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryBound : original.nextIdentity ≤ carryHome.allocation)
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (left right : Reference)
    (lowValue : low = UInt256Proof.SIMD.correctedLo (inputLimb original left) (inputLimb original right))
    (highValue : high = UInt256Proof.SIMD.repairedHi (inputLimb original left) (inputLimb original right))
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 149 args frame [] current = .ok (final, returned) ∧
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
  apply vector128_arm_repair_suffix enabled original entered current inputs outputs output frame args
    call currentCall member authority argument low high highHome highSlot highRead lowRead
    carryHome carry carrySlot carryBound carryRead post
  intro after outputRead afterCall afterAuthority outside advanced
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans outputRead.1
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans outputRead.2
  rw [lowValue, UInt256Proof.SIMD.corrected_lo_words, UInt256Proof.SIMD.arm_repair_words] at lo
  rw [highValue, UInt256Proof.SIMD.repaired_hi_words, UInt256Proof.SIMD.arm_repair_words] at hi
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [output_value_of_packed_halves _ _ _ lo hi, UInt256Proof.sumWords_sum,
      input_limbs_value, input_limbs_value]
  · exact (teardown.access output old 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  · intro id offset earlier untouched
    exact (teardown.cells id earlier offset).trans (outside id offset untouched)

#print axioms vector128_arm_repair_result
end UInt256Proof.Add.Safety

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
