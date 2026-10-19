import UInt256.Methods.Shift.ScalarDispatch
import UInt256.Methods.Shift.ScalarCounts
import UInt256.Methods.Shift.ScalarZero

/-! The canonical count and zero-output steps restated for any body sharing the first 27 instructions;
    the canonical copies stay bound by the production gates. -/

namespace UInt256Proof.Shift.CountPrefix
open CIL.Safety UInt256Model.Safety
open UInt256Proof.Shift.Safety (shiftSpecs)

/-- The canonical count/zero prefix followed by an arbitrary tail. -/
def prefixBody (profile : CIL.FeatureProfile) (tail : List CIL.Op) : CIL.Method :=
  let canonical := UInt256Proof.Shift.Safety.scalarBody profile .left 0
  { canonical with code := canonical.code.take 27 ++ tail }

variable {profile : CIL.FeatureProfile} {tail : List CIL.Op}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (prefixBody profile tail))
include bodyFound

/-- Compute the signed whole-limb count from the actual Int32 argument and
    initialize its private home before any count-dependent branch. -/
theorem shift_count_start (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes (count.sshiftRight 6).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (count.sshiftRight 6).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index (4) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 0 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (prefixBody profile tail) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 0 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 (count.sshiftRight 6)) (count.sshiftRight 6).toNat rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  iterate 3
    apply run_next_exists post found (by rfl)
    shift_pure_step [argument]
  apply run_next_exists post found (by rfl) (stored _ _ _)
  exact done
/-- Both count comparisons read the initialized local and preserve memory.
    The unsigned comparison precedes the signed negative-count test. -/
theorem shift_count_guard (signed : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (word : BitVec 32) (home : Reference)
    (slot : frame.locals[0]? = some (.bytes .word32 home))
    (loaded : read memory home 4 1 = .ok (numberBytes word.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel index
        (if signed then (if 0 ≤ word.toInt then 14 else 10)
         else (if word < BitVec.ofNat 32 4 then 19 else 7))
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (if signed then 7 else 4)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (prefixBody profile tail)) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 word) word.toNat rfl slot loaded
  have found := bodyFound
  cases signed <;> simp only [Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals
    apply run_next_exists post found (by rfl) (load _ _)
    iterate 2
      apply run_next_exists post found (by rfl)
      shift_pure_step []
    exact continuation

/-- Negative counts use their masked low six bits to select zero output or
    the existing historical intra-limb shift convention. -/
theorem shift_negative_count_guard (memory : Memory) (frame : Frame) (args : List Value)
    (count : BitVec 32) (argument : args[1]? = some (.scalar (.i32 count)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel index
        (if count &&& (63 : BitVec 32) != 0 then 17 else 14)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (10) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have found := bodyFound
  iterate 4
    apply run_next_exists post found (by rfl)
    shift_pure_step [argument]
  exact continuation

/-- Reset the whole-limb count only on the selected negative-count route. -/
theorem shift_negative_count_reset (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes 0 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes 0 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index (19) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (17) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (prefixBody profile tail) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 0 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 0) 0 rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  iterate 1
    apply run_next_exists post found (by rfl)
    shift_pure_step []
  apply run_next_exists post found (by rfl) (stored _ _ _)
  exact done

#print axioms shift_negative_count_reset
#print axioms shift_negative_count_guard
#print axioms shift_count_guard
#print axioms shift_count_start

theorem shift_mask_count (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[1]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes (count &&& (63 : BitVec 32)).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (count &&& (63 : BitVec 32)).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index (23) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (19) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (prefixBody profile tail) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 1 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 (count &&& (63 : BitVec 32))) (count &&& (63 : BitVec 32)).toNat rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  iterate 3
    apply run_next_exists post found (by rfl)
    shift_pure_step [argument]
  apply run_next_exists post found (by rfl) (stored _ _ _)
  exact done

theorem shift_complement_count (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (countHome : Reference)
    (countSlot : frame.locals[1]? = some (.bytes .word32 countHome))
    (countRead : read current countHome 4 1 = .ok (numberBytes count.toNat 4))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[2]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes ((63 : BitVec 32) - count).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes ((63 : BitVec 32) - count).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index 27 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (23) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (prefixBody profile tail) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 2 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 ((63 : BitVec 32) - count)) ((63 : BitVec 32) - count).toNat rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (prefixBody profile tail)) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 count) count.toNat rfl countSlot countRead
  iterate 3
    apply run_next_exists post found (by rfl)
    first
    | exact load _ _
    | shift_pure_step []
  apply run_next_exists post found (by rfl) (stored _ _ _)
  exact done

#print axioms shift_mask_count
#print axioms shift_complement_count

/-- Both private count stores retain the previously selected whole-limb count. -/
theorem shift_counts (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (count whole : BitVec 32) (wholeHome : Reference)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (wholeSlot : frame.locals[0]? = some (.bytes .word32 wholeHome))
    (wholeRead : read current wholeHome 4 1 = .ok (numberBytes whole.toNat 4))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ maskHome complementHome after,
      frame.locals[1]? = some (.bytes .word32 maskHome) →
      frame.locals[2]? = some (.bytes .word32 complementHome) →
      read after wholeHome 4 1 = .ok (numberBytes whole.toNat 4) →
      read after maskHome 4 1 = .ok (numberBytes (count &&& (63 : BitVec 32)).toNat 4) →
      read after complementHome 4 1 =
        .ok (numberBytes ((63 : BitVec 32) - (count &&& 63)).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run program fuel index 27 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (19) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply shift_mask_count bodyFound boundary entered current inputs outputs frame args count argument
    call enteredWF homes authority post
  intro maskHome middle maskSlot maskRead preserved middleCall middleAuthority firstWrite
  have keptWhole := write_preserves_disjoint_read firstWrite wholeRead
    (Or.inl (Nat.ne_of_lt (homes.ordered 0 1 .word32 .word32 wholeHome maskHome (by decide) wholeSlot maskSlot)))
  apply shift_complement_count bodyFound boundary entered middle inputs outputs frame args (count &&& 63)
    maskHome maskSlot maskRead middleCall enteredWF homes middleAuthority post
  intro complementHome after complementSlot complementRead retained afterCall afterAuthority secondWrite
  have wholeAfter := write_preserves_disjoint_read secondWrite keptWhole
    (Or.inl (Nat.ne_of_lt (homes.ordered 0 2 .word32 .word32 wholeHome complementHome (by decide) wholeSlot complementSlot)))
  have maskAfter := write_preserves_disjoint_read secondWrite maskRead
    (Or.inl (Nat.ne_of_lt (homes.ordered 1 2 .word32 .word32 maskHome complementHome (by decide) maskSlot complementSlot)))
  exact continuation maskHome complementHome after maskSlot complementSlot wholeAfter maskAfter complementRead
    (preserved.trans retained) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms shift_counts
/-- All signed count branches either reach the zero write or select a bounded
    whole-limb count, retaining the caller memory and private-home authority. -/
theorem shift_count_dispatch (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (zero : ∀ after,
      ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 →
      (0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : BitVec 32) = 0) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run program fuel index (14) args frame [] after =
        .ok (final, returned) ∧ post final returned)
    (ready : ∀ whole reference after,
      whole < BitVec.ofNat 32 4 →
      (whole = count.sshiftRight 6 ∨
        (whole = 0 ∧ (count.sshiftRight 6).toInt < 0 ∧ count &&& (63 : BitVec 32) ≠ 0)) →
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes whole.toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run program fuel index (19) args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel index 0 args frame [] current =
      .ok (final, returned) ∧ post final returned := by
  apply shift_count_start bodyFound boundary entered current inputs outputs frame args count argument
    call enteredWF homes authority post
  intro reference middle slot loaded preserved middleCall middleAuthority written
  have next := (write_extends_allocations _ _ _ _ _ written).next
  apply shift_count_guard bodyFound false middle frame args (count.sshiftRight 6) reference slot loaded post
  by_cases small : count.sshiftRight 6 < BitVec.ofNat 32 4
  · simp only [Bool.false_eq_true, ite_false, ite_eq_left small]
    exact ready _ reference middle small (Or.inl rfl) slot loaded preserved middleCall middleAuthority next
  · simp only [Bool.false_eq_true, ite_false, ite_eq_right small]
    apply shift_count_guard bodyFound true middle frame args (count.sshiftRight 6) reference slot loaded post
    by_cases nonnegative : 0 ≤ (count.sshiftRight 6).toInt
    · simp only [ite_true, ite_eq_left nonnegative]
      exact zero middle small (Or.inl nonnegative) preserved middleCall middleAuthority next
    · simp only [ite_true, ite_eq_right nonnegative]
      apply shift_negative_count_guard bodyFound middle frame args count argument post
      by_cases multiple : count &&& (63 : BitVec 32) = 0
      · simp only [multiple, beq_self_eq_true, Bool.not_true, Bool.false_eq_true]
        exact zero middle small (Or.inr multiple) preserved middleCall middleAuthority next
      · simp only [bne_iff_ne, ite_eq_left multiple]
        apply shift_negative_count_reset bodyFound boundary entered middle inputs outputs frame args
          middleCall enteredWF homes middleAuthority post
        intro resetHome after resetSlot resetRead retained afterCall afterAuthority resetWrite
        exact ready 0 resetHome after (by decide) (Or.inr ⟨rfl, by omega, multiple⟩)
          resetSlot resetRead (preserved.trans retained) afterCall afterAuthority
          (Nat.le_trans next (write_extends_allocations _ _ _ _ _ resetWrite).next)

#print axioms shift_count_dispatch
/-- The zero-output branch initializes all output bytes without requiring them
    to have been initialized before the call, including overlapping views. -/
theorem shift_zero_output (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference)
    (call : CallingConditions program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes 0 32) →
      CallingConditions program after inputs outputs →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = memory.cells id offset) →
      ∃ fuel final returned,
        run program fuel index (16) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (14) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have length : (numberBytes 0 32).length = 32 := by simp [numberBytes]
  obtain ⟨after, written, afterCall, outside, loaded⟩ := call.write_output_slice member 0 (numberBytes 0 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written loaded
  have writtenZero : write memory output (List.replicate 32 0) 1 = .ok after := written
  have done := continuation after loaded afterCall outside
  have formed := call.output_formed member
  have found := bodyFound
  iterate 2
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false }) only
      [step, pureArity, instruction, ordinaryAccessAlignment, argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
        storeValue, referenceAt, writtenZero, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact done

#print axioms shift_zero_output

/-- The zero branch returns normally and retires only private frame storage. -/
theorem shift_zero_finish (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference) (boundary : Nat)
    (call : CallingConditions program memory inputs outputs)
    (member : output ∈ outputs) (argument : args[2]? = some (.reference (.address output)))
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run program fuel index (14) args frame [] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧ read final output 32 1 = .ok (numberBytes 0 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  apply shift_zero_output bodyFound memory inputs outputs frame args output call member argument
  intro after loaded afterCall outside
  have retired := leaveFrame_preserves_memory_below frame after boundary owned
  refine ⟨1, leaveFrame frame after, [], ?_, rfl,
    leaveFrame_preserves_wellFormed frame after afterCall.1.1,
    (retired.read output outputOld 32 1).trans loaded,
    (retired.access output outputOld 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩)), ?_⟩
  · have found := bodyFound
    have fetched : (prefixBody profile tail).code[16]? = some .ret := by rfl
    have returns : (prefixBody profile tail).returnsValue = false := by rfl
    exact run_return found fetched (by rfl) (by rfl)
  · intro id old offset untouched
    exact (retired.cells id old offset).trans (outside id offset untouched)

#print axioms shift_zero_finish
end UInt256Proof.Shift.CountPrefix
