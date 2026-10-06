import UInt256.Methods.Shift.SafetyCountStores
import UInt256.Safety.LimbAccess
import UInt256.Methods.Shift.SafetySetup
import UInt256.Safety.OutputInitialization
import CIL.Safety.AccessBelow
import UInt256.Methods.Shift.SafetyCounts

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Each actual operand load saves an initial-input limb into a private home.
    Caller-byte preservation permits arbitrary overlap with the future output. -/
theorem shift_operand_save (original entered current : Memory)
    (inputs outputs : List Reference) (input : Reference) (frame : Frame) (args : List Value)
    (index : Fin 4) (argument : args[0]? = some (.reference (.address input)))
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs) (member : input ∈ inputs)
    (inputSame : ∀ offset, current.cells input.allocation offset = original.cells input.allocation offset)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[3 + index.val]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes (inputLimb original input index).toNat 8) →
      MemoryBelow original.nextIdentity current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (inputLimb original input index).toNat 8) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc (30 + 3 * index.val)) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc (27 + 3 * index.val)) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have spec : shiftSpecs[3 + index.val]? = some ⟨.word64, .i64 0, 0, rfl⟩ := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨reference, after, slot, loaded, kept, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store Extracted.program shiftBody shiftSpecs original.nextIdentity entered current
      inputs outputs frame currentCall enteredWF homes authority (3 + index.val) _ spec
      (.i64 (inputLimb original input index)) (inputLimb original input index).toNat rfl
  have done := continuation reference after slot loaded kept afterCall afterAuthority written
  have formed := currentCall.input_formed member
  have reading (rest : List Value) : instruction (.field index) (.reference (.address input) :: rest) current =
      .ok (current, .scalar (.i64 (inputLimb original input index)) :: rest) := by
    rw [currentCall.input_field_instruction member index rest]
    simp only [inputLimb, inputSame]
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    dsimp at reading stored done
    iterate 2
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, argument, checkedValue, numericValue, formValue, formed, reading,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists post found (by rfl) (stored _ _ _)
    exact done

#print axioms shift_operand_save
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Saving a later local cannot change any readable earlier numeric home. -/
theorem shift_prior_read (entered before after : Memory) (boundary : Nat) (frame : Frame)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (i j : Nat) (ordered : i < j) (kind : CIL.LocalKind) (source target : Reference)
    (sourceSlot : frame.locals[i]? = some (.bytes kind source))
    (targetSlot : frame.locals[j]? = some (.bytes .word64 target))
    (writtenBytes bytes : List (BitVec 8)) (width alignment : Nat)
    (written : write before target writtenBytes 1 = .ok after)
    (loaded : read before source width alignment = .ok bytes) :
    read after source width alignment = .ok bytes :=
  write_preserves_disjoint_read written loaded
    (Or.inl (Nat.ne_of_lt (homes.ordered i j kind .word64 source target ordered sourceSlot targetSlot)))

/-- Save all four initial operand limbs while retaining the three count homes. -/
theorem shift_operand_snapshots (original entered current : Memory)
    (inputs outputs : List Reference) (input : Reference) (frame : Frame) (args : List Value)
    (argument : args[0]? = some (.reference (.address input)))
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs) (member : input ∈ inputs)
    (inputSame : ∀ offset, current.cells input.allocation offset = original.cells input.allocation offset)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 4, ∃ reference, frame.locals[3 + i.val]? = some (.bytes .word64 reference) ∧
        read after reference 8 1 = .ok (numberBytes (inputLimb original input i).toNat 8)) →
      (∀ i, i < 3 → ∀ reference bytes,
        frame.locals[i]? = some (.bytes .word32 reference) →
        read current reference 4 1 = .ok bytes → read after reference 4 1 = .ok bytes) →
      MemoryBelow original.nextIdentity current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc 39) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 27) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  have old := (call.1.1.1 _ _ present).1
  have sameAfter (after : Memory) (retained : MemoryBelow original.nextIdentity current after) :
      ∀ offset, after.cells input.allocation offset = original.cells input.allocation offset :=
    fun offset => (retained.cells _ old offset).trans (inputSame offset)
  apply shift_operand_save original entered current inputs outputs input frame args 0 argument
    call currentCall member inputSame enteredWF homes authority post
  intro r0 m0 s0 read0 p0 c0 a0 w0
  apply shift_operand_save original entered m0 inputs outputs input frame args 1 argument
    call c0 member (sameAfter _ p0) enteredWF homes a0 post
  intro r1 m1 s1 read1 p1 c1 a1 w1
  apply shift_operand_save original entered m1 inputs outputs input frame args 2 argument
    call c1 member (sameAfter _ (p0.trans p1)) enteredWF homes a1 post
  intro r2 m2 s2 read2 p2 c2 a2 w2
  apply shift_operand_save original entered m2 inputs outputs input frame args 3 argument
    call c2 member (sameAfter _ ((p0.trans p1).trans p2)) enteredWF homes a2 post
  intro r3 m3 s3 read3 p3 c3 a3 w3
  have keep (i : Nat) (bound : i < 3) (reference : Reference) (bytes : List (BitVec 8))
      (slot : frame.locals[i]? = some (.bytes .word32 reference))
      (loaded : read current reference 4 1 = .ok bytes) : read m3 reference 4 1 = .ok bytes := by
    apply shift_prior_read entered m2 m3 original.nextIdentity frame homes i 6 (by omega) .word32 reference r3 slot s3 _ _ 4 1 w3
    apply shift_prior_read entered m1 m2 original.nextIdentity frame homes i 5 (by omega) .word32 reference r2 slot s2 _ _ 4 1 w2
    apply shift_prior_read entered m0 m1 original.nextIdentity frame homes i 4 (by omega) .word32 reference r1 slot s1 _ _ 4 1 w1
    apply shift_prior_read entered current m0 original.nextIdentity frame homes i 3 (by omega) .word32 reference r0 slot s0 _ _ 4 1 w0
    exact loaded
  have snapshots : ∀ i : Fin 4, ∃ reference, frame.locals[3 + i.val]? = some (.bytes .word64 reference) ∧
      read m3 reference 8 1 = .ok (numberBytes (inputLimb original input i).toNat 8) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · refine ⟨r0, s0, ?_⟩
      apply shift_prior_read entered m2 m3 original.nextIdentity frame homes 3 6 (by decide) .word64 r0 r3 s0 s3 _ _ 8 1 w3
      apply shift_prior_read entered m1 m2 original.nextIdentity frame homes 3 5 (by decide) .word64 r0 r2 s0 s2 _ _ 8 1 w2
      apply shift_prior_read entered m0 m1 original.nextIdentity frame homes 3 4 (by decide) .word64 r0 r1 s0 s1 _ _ 8 1 w1
      exact read0
    · refine ⟨r1, s1, ?_⟩
      apply shift_prior_read entered m2 m3 original.nextIdentity frame homes 4 6 (by decide) .word64 r1 r3 s1 s3 _ _ 8 1 w3
      apply shift_prior_read entered m1 m2 original.nextIdentity frame homes 4 5 (by decide) .word64 r1 r2 s1 s2 _ _ 8 1 w2
      exact read1
    · refine ⟨r2, s2, ?_⟩
      apply shift_prior_read entered m2 m3 original.nextIdentity frame homes 5 6 (by decide) .word64 r2 r3 s2 s3 _ _ 8 1 w3
      exact read2
    · refine ⟨r3, s3, ?_⟩
      exact read3
  exact continuation m3 snapshots keep (((p0.trans p1).trans p2).trans p3) c3 a3
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (Nat.le_trans (write_extends_allocations _ _ _ _ _ w2).next
          (write_extends_allocations _ _ _ _ _ w3).next)))

#print axioms shift_operand_snapshots
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Separation is required only when the extracted body writes before reading
    its operand. Returning operators establish it from their private output. -/
def InitializationAllowed (input output : Reference) : Prop :=
  shiftCountEnd = shiftSnapshotPc ∨ input.allocation ≠ output.allocation

theorem shift_initialization (memory : Memory) (input output : Reference)
    (frame : Frame) (args : List Value) (inputs outputs : List Reference)
    (argument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions Extracted.program memory inputs outputs) (member : output ∈ outputs)
    (allowed : InitializationAllowed input output) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      CallingConditions Extracted.program after inputs outputs →
      (∀ offset, after.cells input.allocation offset = memory.cells input.allocation offset) →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = memory.cells id offset) →
      (∀ watermark, AccessBelow watermark memory after) →
      (∀ reference width alignment bytes, reference.allocation ≠ output.allocation →
        read memory reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      memory.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run Extracted.program fuel shiftIndex (shiftPc 27) args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run Extracted.program fuel shiftIndex shiftCountEnd args frame [] memory =
      .ok (final, returned) ∧ post final returned := by
  first
  | have same : shiftCountEnd = shiftPc 27 := by rfl
    rw [same]
    exact continuation memory call (fun _ => rfl) (fun _ _ _ => rfl)
      (fun watermark => (MemoryBelow.refl watermark memory).accessBelow) (fun _ _ _ _ _ loaded => loaded) (Nat.le_refl _)
  | apply output_initialization_prefix Extracted.program shiftIndex shiftCountEnd 2 shiftBody frame args
      memory inputs outputs output 0 call member (by rfl) argument
      (by
        intro i
        have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) post
    intro after written valid outside
    have different : input.allocation ≠ output.allocation := allowed.resolve_left (by decide)
    apply continuation after valid (fun offset => outside input.allocation offset (Or.inl different)) outside
      (fun watermark => write_preserves_access_below written watermark) ?_ (write_extends_allocations _ _ _ _ _ written).next
    intro reference width alignment bytes separate loaded
    exact write_preserves_disjoint_read written loaded (Or.inl separate)

#print axioms shift_initialization
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Count preparation, checked output initialization and original operand snapshots. -/
theorem shift_prepared (original entered current : Memory)
    (inputs outputs : List Reference) (input output : Reference) (frame : Frame) (args : List Value)
    (count whole : BitVec 32) (wholeHome : Reference)
    (inputArgument : args[0]? = some (.reference (.address input)))
    (countArgument : args[1]? = some (.scalar (.i32 count)))
    (outputArgument : args[2]? = some (.reference (.address output)))
    (outputMember : output ∈ outputs) (allowed : InitializationAllowed input output)
    (wholeSlot : frame.locals[0]? = some (.bytes .word32 wholeHome))
    (wholeRead : read current wholeHome 4 1 = .ok (numberBytes whole.toNat 4))
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs) (member : input ∈ inputs)
    (preserved : MemoryBelow original.nextIdentity original current)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ maskHome complementHome after,
      frame.locals[1]? = some (.bytes .word32 maskHome) →
      frame.locals[2]? = some (.bytes .word32 complementHome) →
      read after wholeHome 4 1 = .ok (numberBytes whole.toNat 4) →
      read after maskHome 4 1 = .ok (numberBytes (count &&& (63 : BitVec 32)).toNat 4) →
      read after complementHome 4 1 =
        .ok (numberBytes ((63 : BitVec 32) - (count &&& 63)).toNat 4) →
      (∀ i : Fin 4, ∃ reference, frame.locals[3 + i.val]? = some (.bytes .word64 reference) ∧
        read after reference 8 1 = .ok (numberBytes (inputLimb original input i).toNat 8)) →
      (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
        after.cells id offset = current.cells id offset) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc 39) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 19) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply shift_counts original.nextIdentity entered current inputs outputs frame args count whole
    wholeHome countArgument wholeSlot wholeRead currentCall enteredWF homes authority post
  intro maskHome complementHome middle maskSlot complementSlot wholeRead maskRead complementRead p c a n
  apply shift_initialization middle input output frame args inputs outputs outputArgument c outputMember allowed post
  intro initialized initializedCall inputSame outside initializedAccess keptReads next
  obtain ⟨inputAllocation, inputPresent, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  have inputOld := (call.1.1.1 _ _ inputPresent).1
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  have keepCount (i : Nat) (reference : Reference) (bytes : List (BitVec 8))
      (slot : frame.locals[i]? = some (.bytes .word32 reference))
      (loaded : read middle reference 4 1 = .ok bytes) : read initialized reference 4 1 = .ok bytes := by
    apply keptReads reference 4 1 bytes _ loaded
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld (homes.home_bound i .word32 reference slot)))
  apply shift_operand_snapshots original entered initialized inputs outputs input frame args inputArgument
    call initializedCall member
    (fun offset => (inputSame offset).trans ((preserved.trans p).cells _ inputOld offset))
    enteredWF homes (a.trans (initializedAccess _)) post
  intro after snapshots keep q d b m
  refine continuation maskHome complementHome after maskSlot complementSlot
    (keep 0 (by decide) wholeHome _ wholeSlot (keepCount 0 wholeHome _ wholeSlot wholeRead))
    (keep 1 (by decide) maskHome _ maskSlot (keepCount 1 maskHome _ maskSlot maskRead))
    (keep 2 (by decide) complementHome _ complementSlot (keepCount 2 complementHome _ complementSlot complementRead))
    snapshots ?_ d b (Nat.le_trans n (Nat.le_trans next m))
  intro id old offset untouched
  exact (q.cells id old offset).trans ((outside id offset untouched).trans (p.cells id old offset))

#print axioms shift_prepared
end UInt256Proof.Shift.Safety
