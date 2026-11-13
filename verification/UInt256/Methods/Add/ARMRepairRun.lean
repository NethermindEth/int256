import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.ARMRepairCarry

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete repaired output/return suffix. -/
theorem vector128_arm_repair_suffix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode)) (returns : body.returnsValue = true) (enabled : body.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
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
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      current.nextIdentity ≤ after.nextIdentity →
      post (leaveFrame frame after)
        [.scalar (.i32 (if CIL.Vector.lane64 carry 1 > BitVec.ofNat 64 0 then 1 else 0))]) :
    ∃ fuel final returned,
      run program fuel method 149 args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨after, written, highOutput, afterCall, afterAuthority, outside, privateReads,
    advanced⟩ := output_half_update program original entered current inputs outputs output 1 high
      call currentCall member authority
  simp only [Fin.val_one, Nat.mul_one] at written highOutput
  have lowOutput := write_preserves_disjoint_read written lowRead (Or.inr (Or.inl (by simp)))
  have loadHigh : ∀ pc stack, step body (.local 11) pc args frame stack current =
      .ok (.next (pc + 1) (.scalar (.v128 high) :: stack) frame current) := fun pc stack =>
    step_load_numeric_local .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have loadCarry : ∀ pc stack, step body (.local 7) pc args frame stack after =
      .ok (.next (pc + 1) (.scalar (.v128 carry) :: stack) frame after) := fun pc stack =>
    step_load_numeric_local .vector128 (.v128 carry) carry.toNat rfl carrySlot
      (privateReads carryHome 16 1 _ carryBound carryRead)
  have address := currentCall.output_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at address
  cil_contract_steps [found, code, returns, enabled, argument, loadHigh, loadCarry,
    currentCall.output_formed member, written, address]
  simpa [CIL.NarrowKind.extend_ite_ofNat_one_zero, CIL.NarrowKind.extend_ite_one_zero] using
    continuation after ⟨lowOutput, highOutput⟩ afterCall afterAuthority outside advanced

end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Repaired output halves encode the independent initial-input sum, and caller value/access/footprint guarantees survive the private frame return. -/
theorem vector128_arm_repair_result (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode)) (returns : body.returnsValue = true) (enabled : body.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
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
      run program fuel method 149 args frame [] current = .ok (final, returned) ∧
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
  apply vector128_arm_repair_suffix program body method found code returns enabled original entered current inputs outputs output frame args
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
      (afterCall.1.writable (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  · intro id offset earlier untouched
    exact (teardown.cells id earlier offset).trans (outside id offset untouched)

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete ARM repair branch from saved initial-input snapshots to normal return, retaining the independent sum and caller memory guarantees. -/
theorem vector128_arm_repair_run (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode))
    (returns : body.returnsValue = true)  (enabled : body.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (left right output : Reference) (frame : Frame) (root : Option ManagedReference)
    (slots : List LocalSlot) (layout : frame.locals = .root root :: slots) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
      (homes : NumericHomes entered original.nextIdentity armSpecs slots)
    (authority : AccessBelow entered.nextIdentity entered current) (member : output ∈ outputs)
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (vector128DecisionValues body.profile.advSimd original left right flag i).toNat 16))
    (lowRead : read current output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16))
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 113 args frame [] current = .ok (final, returned) ∧
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
  apply vector128_arm_repair_checked program body method found code enabled original.nextIdentity
    entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority flag flagFit flagArg (vector128DecisionValues body.profile.advSimd original left right flag) rfl snapshots post
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
    vector128_arm_repair_result program body method found code returns enabled original entered after inputs outputs output frame args
      call afterCall member afterAuthority outputArg (vector128SnapshotValue original left right 9)
      (armRepairSnapshot (vector128DecisionValues body.profile.advSimd original left right flag) 10)
      highHome actualHigh highRead savedLow carryHome
      (armRepairSnapshot (vector128DecisionValues body.profile.advSimd original left right flag) 6) actualCarry
      (homes.home_bound 6 .vector128 carryHome carrySlot) carryRead left right
      (vector128_snapshot_low original left right) (vector128_repaired_snapshot_high body.profile.advSimd original left right flag) owned
  rw [vector128_snapshot_repaired_flag] at scalar
  exact ⟨fuel, final, returned, executed, scalar, result, writable,
    fun id offset bound untouched => (outside id offset bound untouched).trans (preserved.cells id bound offset)⟩

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128RepairStart (body : CIL.Method) : Nat := if body.profile.advSimd then 113 else 162

/-- Follow the extracted repair ISA guard without changing memory or locals. -/
theorem vector128_repair_dispatch (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 111 ([.feature .advSimd, .brzero 162])) (memory : Memory) (frame : Frame) (args : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (vector128RepairStart body) args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 111 args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  cases selected : body.profile.advSimd <;> simp only [vector128RepairStart, selected, Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals repeat' first
    | exact continuation
    | (apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
       simp (config := { implicitDefEqProofs := false })
         [step, cil_guard, observerCount, selected, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
           numericValue, checkedValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

end UInt256Proof.Add.Safety
