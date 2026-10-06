import UInt256.Methods.Shift.SafetyCount
import CIL.Safety.ReturnMemory
import UInt256.Methods.Shift.SafetyStore
import UInt256.Methods.Shift.SafetyCountMath
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- The zero-output branch initializes all output bytes without requiring them
    to have been initialized before the call, including overlapping views. -/
theorem shift_zero_output (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes 0 32) →
      CallingConditions Extracted.program after inputs outputs →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = memory.cells id offset) →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc 16) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 14) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have length : (numberBytes 0 32).length = 32 := by simp [numberBytes]
  obtain ⟨after, written, afterCall, outside, loaded⟩ := call.write_output_slice member 0 (numberBytes 0 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written loaded
  have done := continuation after loaded afterCall outside
  have formed := call.output_formed member
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  iterate 2
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
        storeValue, referenceAt, written, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact done

#print axioms shift_zero_output

/-- The zero branch returns normally and retires only private frame storage. -/
theorem shift_zero_finish (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference) (boundary : Nat)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 14) args frame [] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧ read final output 32 1 = .ok (numberBytes 0 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  apply shift_zero_output memory inputs outputs frame args output call member argument
  intro after loaded afterCall outside
  have retired := leaveFrame_preserves_memory_below frame after boundary owned
  refine ⟨1, leaveFrame frame after, [], ?_, rfl,
    leaveFrame_preserves_wellFormed frame after afterCall.1.1,
    (retired.read output outputOld 32 1).trans loaded,
    (retired.access output outputOld 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩)), ?_⟩
  · have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
    have fetched : shiftBody.code[shiftPc 16]? = some .ret := by rfl
    have returns : shiftBody.returnsValue = false := by rfl
    simp [run, found, fetched, returns, step, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro id old offset untouched
    exact (retired.cells id old offset).trans (outside id offset untouched)

#print axioms shift_zero_finish
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- All signed count branches either reach the zero write or select a bounded
    whole-limb count, retaining the caller memory and private-home authority. -/
theorem shift_count_dispatch (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (zero : ∀ after,
      ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 →
      (0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : BitVec 32) = 0) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run Extracted.program fuel shiftIndex (shiftPc 14) args frame [] after =
        .ok (final, returned) ∧ post final returned)
    (ready : ∀ whole reference after,
      whole < BitVec.ofNat 32 4 →
      (whole = count.sshiftRight 6 ∨
        (whole = 0 ∧ (count.sshiftRight 6).toInt < 0 ∧ count &&& (63 : BitVec 32) ≠ 0)) →
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes whole.toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run Extracted.program fuel shiftIndex (shiftPc 19) args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run Extracted.program fuel shiftIndex 0 args frame [] current =
      .ok (final, returned) ∧ post final returned := by
  apply shift_count_start boundary entered current inputs outputs frame args count argument
    call enteredWF homes authority post
  intro reference middle slot loaded preserved middleCall middleAuthority written
  have next := (write_extends_allocations _ _ _ _ _ written).next
  apply shift_count_guard false middle frame args (count.sshiftRight 6) reference slot loaded post
  by_cases small : count.sshiftRight 6 < BitVec.ofNat 32 4
  · simp only [Bool.false_eq_true, ite_false, ite_eq_left small]
    exact ready _ reference middle small (Or.inl rfl) slot loaded preserved middleCall middleAuthority next
  · simp only [Bool.false_eq_true, ite_false, ite_eq_right small]
    apply shift_count_guard true middle frame args (count.sshiftRight 6) reference slot loaded post
    by_cases nonnegative : 0 ≤ (count.sshiftRight 6).toInt
    · simp only [ite_true, ite_eq_left nonnegative]
      exact zero middle small (Or.inl nonnegative) preserved middleCall middleAuthority next
    · simp only [ite_true, ite_eq_right nonnegative]
      apply shift_negative_count_guard middle frame args count argument post
      by_cases multiple : count &&& (63 : BitVec 32) = 0
      · simp only [multiple, beq_self_eq_true, Bool.not_true, Bool.false_eq_true]
        exact zero middle small (Or.inr multiple) preserved middleCall middleAuthority next
      · simp only [bne_iff_ne, ite_eq_left multiple]
        apply shift_negative_count_reset boundary entered middle inputs outputs frame args
          middleCall enteredWF homes middleAuthority post
        intro resetHome after resetSlot resetRead retained afterCall afterAuthority resetWrite
        exact ready 0 resetHome after (by decide) (Or.inr ⟨rfl, by omega, multiple⟩)
          resetSlot resetRead (preserved.trans retained) afterCall afterAuthority
          (Nat.le_trans next (write_extends_allocations _ _ _ _ _ resetWrite).next)

#print axioms shift_count_dispatch
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- From the prepared private snapshots, finish the selected shift, including
    the real storage call and normal return. -/
theorem shift_nonzero_finish (whole : Fin 4) (memory : Memory) (frame : Frame)
    (inputs : List Reference) (args : List Value) (output : Reference) (count : BitVec 32)
    (wholeHome maskHome complementHome : Reference)
    (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64) (boundary : Nat)
    (argument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions Extracted.program memory inputs [output])
    (wholeSlot : frame.locals[0]? = some (.bytes .word32 wholeHome))
    (maskSlot : frame.locals[1]? = some (.bytes .word32 maskHome))
    (complementSlot : frame.locals[2]? = some (.bytes .word32 complementHome))
    (wholeRead : read memory wholeHome 4 1 = .ok (numberBytes whole.val 4))
    (maskRead : read memory maskHome 4 1 = .ok (numberBytes (count &&& (63 : BitVec 32)).toNat 4))
    (complementRead : read memory complementHome 4 1 =
      .ok (numberBytes ((63 : BitVec 32) - (count &&& 63)).toNat 4))
    (slots : ∀ i : Fin 4, frame.locals[3 + i.val]? = some (.bytes .word64 (homes i)))
    (reads : ∀ i : Fin 4, read memory (homes i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 39) args frame [] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧
      inputValue final output = shiftValue shiftDirection (UInt256Model.value words) (64 * whole.val + count.toNat % 64) ∧
      access final output 32 1 true = .ok () ∧
      (∃ bytes, read final output 32 1 = .ok bytes) ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  apply shift_output_dispatch whole memory frame args wholeHome wholeSlot wholeRead
  apply shift_output_arguments whole memory frame args output (count &&& 63) (63 - (count &&& 63))
    maskHome complementHome homes words argument (call.output_formed (by simp))
    maskSlot complementSlot maskRead complementRead slots reads
  let outputWords := outputWords shiftDirection whole words (count &&& 63) (63 - (count &&& 63))
  obtain ⟨fuel, final, returned, executed, empty, wf, result, writable, readable, footprint⟩ :=
    shift_store_return whole memory inputs frame args output boundary
      (outputWords.getD 0 0) (outputWords.getD 1 0) (outputWords.getD 2 0) (outputWords.getD 3 0)
      call outputOld owned
  have stack : outputWords.reverse.map (fun w => Value.scalar (.i64 w)) =
      [.scalar (.i64 (outputWords.getD 3 0)), .scalar (.i64 (outputWords.getD 2 0)),
       .scalar (.i64 (outputWords.getD 1 0)), .scalar (.i64 (outputWords.getD 0 0))] := by
    have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
    cases shiftDirection <;> rcases cases with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨fuel, final, returned, ?_, empty, wf, ?_, writable, readable, footprint⟩
  · change run _ _ _ _ _ _ (outputWords.reverse.map _ ++ _) _ = _
    rw [stack]
    exact executed
  · have packed := pack_value (fun i : Fin 4 => outputWords.getD i.val 0)
    change pack (outputWords.getD 0 0) (outputWords.getD 1 0)
      (outputWords.getD 2 0) (outputWords.getD 3 0) = _ at packed
    exact result.trans (packed.symm.trans (shift_output_value shiftDirection whole words count))

#print axioms shift_nonzero_finish
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

def ShiftResult (original final : Memory) (returned : List Value)
    (input output : Reference) (count : BitVec 32) : Prop :=
  returned = [] ∧ final.WellFormed ∧
  inputValue final output = result shiftDirection (inputValue original input) count ∧
  access final output 32 1 true = .ok () ∧
  (∃ bytes, read final output 32 1 = .ok bytes) ∧
  (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset)

theorem zero_read_value (memory : Memory) (output : Reference)
    (loaded : read memory output 32 1 = .ok (numberBytes 0 32)) : inputValue memory output = 0 := by
  have decoded := congrArg CIL.Safety.byteNumber (read_result_snapshot loaded)
  rw [byteNumber_numberBytes, byteNumber_snapshot
    (fun offset => (memory.cells output.allocation offset).bits) output.offset 32] at decoded
  simp only [Nat.zero_mod] at decoded
  change BitVec.ofNat 256 (UInt256Model.byteNumber
    (fun offset => (memory.cells output.allocation offset).bits) output.offset 32) = _
  rw [← decoded]
  rfl

/-- Execute the complete body from a valid private frame. The result is stated
    on the initial caller operand, with the public full-signed-count semantics. -/
theorem shift_body (original entered current : Memory) (input output : Reference)
    (count : BitVec 32) (frame : Frame) (args : List Value)
    (inputArgument : args[0]? = some (.reference (.address input)))
    (countArgument : args[1]? = some (.scalar (.i32 count)))
    (outputArgument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions Extracted.program original [input] [output])
    (currentCall : CallingConditions Extracted.program current [input] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (allowed : InitializationAllowed input output) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex 0 args frame [] current = .ok (final, returned) ∧
      ShiftResult original final returned input output count := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  apply shift_count_dispatch original.nextIdentity entered current [input] [output] frame args count
    countArgument currentCall enteredWF homes authority
  · intro after large selected retained valid access next
    obtain ⟨fuel, final, returned, executed, empty, wf, loaded, writable, outside⟩ :=
      shift_zero_finish after [input] [output] frame args output original.nextIdentity valid
        (by simp) outputArgument outputOld owned
    refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, ⟨_, loaded⟩, ?_⟩
    · rw [zero_read_value final output loaded]
      simp only [result, shift_zero_count count large selected]
    · intro id old offset untouched
      exact (outside id old offset untouched).trans
        ((preserved.trans retained).cells id old offset)
  · intro whole wholeHome after small selected wholeSlot wholeRead retained valid access next
    apply shift_prepared original entered after [input] [output] input output frame args count whole wholeHome
      inputArgument countArgument outputArgument (by simp) allowed wholeSlot wholeRead call valid (by simp)
      (preserved.trans retained) enteredWF homes access
    intro maskHome complementHome ready maskSlot complementSlot wholeRead maskRead complementRead snapshots kept readyCall readyAccess readyNext
    let bounded : Fin 4 := ⟨whole.toNat, small⟩
    let references : Fin 4 → Reference := fun i => (snapshots i).choose
    have slots := fun i => (snapshots i).choose_spec.1
    have reads := fun i => (snapshots i).choose_spec.2
    obtain ⟨fuel, final, returned, executed, empty, wf, calculated, writable, readable, outside⟩ :=
      shift_nonzero_finish bounded ready frame [input] args output count wholeHome maskHome complementHome
        references (inputLimb original input) original.nextIdentity outputArgument readyCall
        wholeSlot maskSlot complementSlot wholeRead maskRead complementRead slots reads outputOld owned
    refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, readable, ?_⟩
    · rw [input_limbs_value] at calculated
      have selectedCount := shift_selected_count count whole small selected
      cases direction : shiftDirection <;>
        simpa only [result, selectedCount, shiftValue, direction] using calculated
    · intro id old offset untouched
      exact (outside id old offset untouched).trans
        ((kept id old offset untouched).trans ((preserved.trans retained).cells id old offset))

#print axioms shift_body
end UInt256Proof.Shift.Safety
