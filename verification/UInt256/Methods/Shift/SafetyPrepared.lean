import UInt256.Methods.Shift.SafetyCounts
import UInt256.Methods.Shift.SafetySnapshots
import UInt256.Methods.Shift.SafetyInitialization

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
