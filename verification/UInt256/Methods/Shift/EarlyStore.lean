import UInt256.Methods.Shift.CountPrefix
import UInt256.Methods.Shift.ScalarContract
import UInt256.Methods.Shift.DisjointContract
import UInt256.Methods.Shift.LeftFlow
import UInt256.Methods.StorageFlow

namespace UInt256Proof.Shift.Variant
open CIL.Safety UInt256Model.Safety UInt256Proof.Transport UInt256Proof.Shift.Safety

/-- Eight instructions zeroing the first output limb before any input limb is read. -/
def earlyStoreOps : List CIL.Op :=
  [.arg 2, .skipInit, .arg 2, .fieldAddress 0, .memory .asRef, .const32 0, .convI8, .store64]

/-- The left body with `earlyStoreOps` inserted after the count prefix; valid only for disjoint outputs. -/
def earlyBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method :=
  let canonical := scalarBody profile .left storage
  { canonical with code := (canonical.code.take 27 ++ earlyStoreOps) ++
      (canonical.code.drop 27).map (relocateOp (· + 8)) }

theorem early_suffix_lookup (profile : CIL.FeatureProfile) (storage pc : Nat) (inside : 27 ≤ pc) :
    (earlyBody profile storage).code[pc + 8]? =
      ((scalarBody profile .left storage).code[pc]?).map (relocateOp (· + 8)) := by
  dsimp only [earlyBody]
  rw [List.getElem?_append_right]
  · have length : ((scalarBody profile .left storage).code.take 27 ++ earlyStoreOps).length = 35 := rfl
    rw [length, List.getElem?_map, List.getElem?_drop]
    have same : 27 + (pc + 8 - 35) = pc := by omega
    rw [same]
  · change 35 ≤ pc + 8
    omega

/-- The inserted instructions write eight zero bytes at the output and leave the stack empty. -/
theorem early_store_prefix (profile : CIL.FeatureProfile) (program : CIL.Program) (index storage fuel : Nat)
    (found : program[index]? = some (earlyBody profile storage))
    (memory after : Memory) (input output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program memory [input] [output])
    (argument : args[2]? = some (.reference (.address output)))
    (written : write memory output (numberBytes 0 8) 1 = .ok after) :
    run program (fuel + 8) index 27 args frame [] memory = run program fuel index 35 args frame [] after := by
  have formed := call.output_formed (by simp : output ∈ [output])
  obtain ⟨allocation, ready⟩ := access_requirements (call.1.2.2 (wordView output) (by simp))
  have addZero : add memory output 1 (BitVec.ofNat 64 0) = .ok output := by
    simpa [wordView] using ready.add_slice call.1.1 1 0 1 (by decide) (by dsimp [wordView] at ready ⊢; omega)
  iterate 8
    apply Eq.trans
    · apply run_next found (by rfl)
      first
      | rfl
      | (simp (config := { implicitDefEqProofs := false }) [step, pureArity, instruction, staticInstruction,
          memoryInstruction, argument, checkedValue, formValue, formed, checkedAt, addZero, storeValue,
          referenceAt, ordinaryAccessAlignment, written,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  rfl

/-- After the private frame is set up, the early-store body reaches the canonical result for disjoint outputs. -/
theorem early_body_run (profile : CIL.FeatureProfile) (storageBody : CIL.Method) (callFree : CallFree storageBody)
    (storeOf : ∀ program : CIL.Program, ∀ storage, program[storage]? = some storageBody → StoreLimbsContract program storage)
    (program : CIL.Program) (index storage : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (earlyBody profile storage))
    (storageFound : program[storage]? = some storageBody)
    (original entered current : Memory) (input output : Reference) (count : BitVec 32) (frame : Frame) (args : List Value)
    (inputArgument : args[0]? = some (.reference (.address input)))
    (countArgument : args[1]? = some (.scalar (.i32 count)))
    (outputArgument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [input] [output])
    (currentCall : CallingConditions program current [input] [output])
    (disjoint : output.allocation ≠ input.allocation)
    (preserved : MemoryBelow original.nextIdentity original current)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned, run program fuel index 0 args frame [] current = .ok (final, returned) ∧
      ShiftResult (direction := .left) original final returned input output count := by
  let virtual := program.set index (scalarBody profile .left storage)
  have indexBound := (List.getElem?_eq_some_iff.mp found).choose
  have virtualFound : virtual[index]? = some (scalarBody profile .left storage) := List.getElem?_set_self indexBound
  have virtualStorage : virtual[storage]? = some storageBody := by
    simpa only [virtual, List.getElem?_set_ne distinct] using storageFound
  have store : StoreLimbsContract virtual storage := storeOf virtual storage virtualStorage
  have virtualCall (memory : Memory) (valid : CallingConditions program memory [input] [output]) :
      CallingConditions virtual memory [input] [output] :=
    set_calling (source := scalarBody profile .left storage) found rfl valid
  have prefixFound : program[index]? = some (CountPrefix.prefixBody profile
      (earlyStoreOps ++ (scalarBody profile .left storage).code.drop 27 |>.map (relocateOp (· + 8)))) := found
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  obtain ⟨inputAllocation, inputPresent, _, _⟩ := formed_reference_live _ _ _ (call.input_formed (by simp : input ∈ [input]))
  have inputOld : input.allocation < original.nextIdentity := (call.1.1.1 _ _ inputPresent).1
  apply CountPrefix.shift_count_dispatch prefixFound original.nextIdentity entered current [input] [output] frame args count
    countArgument currentCall enteredWF homes authority
  · intro after large selected retained valid access next
    obtain ⟨fuel, final, returned, executed, empty, wf, loaded, writable, outside⟩ :=
      CountPrefix.shift_zero_finish prefixFound after [input] [output] frame args output original.nextIdentity valid
        (by simp) outputArgument outputOld owned
    refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, ⟨_, loaded⟩, ?_⟩
    · rw [zero_read_value final output loaded]
      simp only [UInt256Proof.Shift.result, shift_zero_count count large selected]
    · intro id old offset untouched
      exact (outside id old offset untouched).trans ((preserved.trans retained).cells id old offset)
  · intro whole wholeHome after small selected wholeSlot wholeRead retained valid access next
    apply CountPrefix.shift_counts prefixFound original.nextIdentity entered after [input] [output] frame args count whole
      wholeHome countArgument wholeSlot wholeRead valid enteredWF homes access
    intro maskHome complementHome ready maskSlot complementSlot wholeRead maskRead complementRead kept readyCall
      readyAccess readyNext
    obtain ⟨stored, written, storedCall, earlyOutside, _⟩ := readyCall.write_output_slice (by simp : output ∈ [output]) 0
      (numberBytes 0 8) (by simp [numberBytes]) (by simp [numberBytes])
    simp only [Nat.add_zero] at written
    have beforeStore := (preserved.trans retained).trans kept
    have inputSame : ∀ offset, stored.cells input.allocation offset = original.cells input.allocation offset := by
      intro offset
      exact (write_other_allocation _ _ _ _ _ _ _ written (Ne.symm disjoint)).trans (beforeStore.cells _ inputOld offset)
    have keepCount (i : Nat) (reference : Reference) (bytes : List (BitVec 8))
        (slot : frame.locals[i]? = some (.bytes .word32 reference)) (loaded : read ready reference 4 1 = .ok bytes) :
        read stored reference 4 1 = .ok bytes :=
      write_preserves_disjoint_read written loaded (Or.inl (Ne.symm (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le outputOld (homes.home_bound i .word32 reference slot)))))
    have storedAuthority := readyAccess.trans (write_preserves_access_below written entered.nextIdentity)
    have suffix : ∃ fuel final returned, run virtual fuel index 27 args frame [] stored = .ok (final, returned) ∧
        ShiftResult (direction := .left) original final returned input output count := by
      apply shift_operand_snapshots virtualFound original entered stored [input] [output] input frame args inputArgument
        (virtualCall original call) (virtualCall stored storedCall) (by simp) inputSame enteredWF homes storedAuthority
      intro ready snapshots countReads snapshotKept snapshotCall snapshotAccess snapshotNext
      let bounded : Fin 4 := ⟨whole.toNat, small⟩
      let references : Fin 4 → Reference := fun i => (snapshots i).choose
      have slots := fun i => (snapshots i).choose_spec.1
      have reads := fun i => (snapshots i).choose_spec.2
      obtain ⟨fuel, final, returned, executed, empty, wf, calculated, writable, readable, outside⟩ :=
        shift_nonzero_finish virtualFound store bounded ready frame [input] args output count wholeHome maskHome
          complementHome references (inputLimb original input) original.nextIdentity outputArgument snapshotCall
          wholeSlot maskSlot complementSlot
          (countReads 0 (by decide) wholeHome _ wholeSlot (keepCount 0 _ _ wholeSlot wholeRead))
          (countReads 1 (by decide) maskHome _ maskSlot (keepCount 1 _ _ maskSlot maskRead))
          (countReads 2 (by decide) complementHome _ complementSlot (keepCount 2 _ _ complementSlot complementRead))
          slots reads outputOld owned
      refine ⟨fuel, final, returned, executed, empty, wf, ?_, writable, readable, ?_⟩
      · have model : UInt256Model.value (inputLimb original input) = inputValue original input := UInt256Proof.input_value _ _
        rw [model] at calculated
        have selectedCount := shift_selected_count count whole small selected
        simpa only [UInt256Proof.Shift.result, selectedCount, shiftValue] using calculated
      · intro id old offset untouched
        exact (outside id old offset untouched).trans ((snapshotKept.cells id old offset).trans
          ((earlyOutside id offset untouched).trans (beforeStore.cells id old offset)))
    obtain ⟨fuel, final, returned, executed, post⟩ := suffix
    have relation := suffix_correspondence program index storage 27 (· + 8) (scalarBody profile .left storage)
      (earlyBody profile storage) storageBody distinct found storageFound callFree (fun _ _ => rfl)
      (fun _ _ _ _ _ _ => rfl) (fun _ _ => by omega)
      (fun pc op lower opcode => by
        have suffixOpcode : ((scalarBody profile .left storage).code.drop 27)[pc - 27]? = some op := by
          rw [List.getElem?_drop]
          have same : 27 + (pc - 27) = pc := by omega
          simpa only [same] using opcode
        exact ⟨left_supported profile storage op (List.mem_of_getElem? opcode),
          left_suffix_flow_inputs profile storage op (List.mem_of_getElem? suffixOpcode)⟩)
      (fun pc lower => early_suffix_lookup profile storage pc lower)
    have moved := run_success_transport virtual program _ _ relation fuel index 27 args frame [] stored final returned
      (Or.inr ⟨rfl, Nat.le_refl 27⟩) executed
    have moved' : run program fuel index 35 args frame [] stored = .ok (final, returned) := by simpa [suffixMap] using moved
    exact ⟨fuel + 8, final, returned, (early_store_prefix profile program index storage fuel found ready stored input
      output frame args readyCall outputArgument written).trans moved', post⟩

theorem early_contract (profile : CIL.FeatureProfile) (storageBody : CIL.Method) (callFree : CallFree storageBody)
    (storeOf : ∀ program : CIL.Program, ∀ storage, program[storage]? = some storageBody → StoreLimbsContract program storage)
    (program : CIL.Program) (index storage : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (earlyBody profile storage))
    (storageFound : program[storage]? = some storageBody) :
    DisjointShiftContract .left program index := by
  intro memory input count output call disjoint
  have checked : (shiftArguments input count output).mapM (checkedValue memory) =
      .ok (shiftArguments input count output) := by
    have fi := call.input_formed (by simp : input ∈ [input])
    have fo := call.output_formed (by simp : output ∈ [output])
    simp [shiftArguments, checkedValue, numericValue, formValue, checkedAt, fi, fo,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨frame, entered, setup, homes, preserved, wf⟩ :=
    scalar_frame_setup profile .left storage memory (shiftArguments input count output) call.1.1
  have targetSetup : enterFrame (earlyBody profile storage) (shiftArguments input count output) memory =
    .ok (frame, entered) := setup
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked targetSetup
  have fresh := enterFrame_fresh _ _ _ _ _ targetSetup
  obtain ⟨fuel, final, returned, executed, empty, finalWF, value, writable, readable, footprint⟩ :=
    early_body_run profile storageBody callFree storeOf program index storage distinct found storageFound memory entered
      entered input output count frame (shiftArguments input count output) rfl rfl rfl call
      (call.after_frame_setup targetSetup) disjoint preserved wf homes
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow (fun id member => (fresh.2 id member).1)
  subst returned
  exact ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked targetSetup live executed,
    value, writable, readable, footprint⟩

theorem scalar_early_contract (profile : CIL.FeatureProfile) (scalar : profile.vector256Accelerated = false)
    (program : CIL.Program) (index storage : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (earlyBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.StorageScalar.body profile)) :
    DisjointShiftContract .left program index :=
  early_contract profile _ (scalar_storage_call_free profile)
    (fun program storage found => UInt256Proof.StorageScalar.store_limbs_readable_contract profile scalar program storage found)
    program index storage distinct found storageFound

theorem vector_early_contract (profile : CIL.FeatureProfile) (vector : profile.vector256Accelerated = true)
    (program : CIL.Program) (index storage : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (earlyBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.StorageVector.body profile)) :
    DisjointShiftContract .left program index :=
  early_contract profile _ (vector_storage_call_free profile)
    (fun program storage found => UInt256Proof.StorageVector.store_limbs_readable_contract profile vector program storage found)
    program index storage distinct found storageFound

#print axioms scalar_early_contract
#print axioms vector_early_contract
end UInt256Proof.Shift.Variant
