import UInt256.Methods.Shift.ScalarContract
import UInt256.Methods.Shift.LeftFlow
import UInt256.Methods.StorageFlow
import UInt256.Safety.RegionSuffix

namespace UInt256Proof.Shift.Variant
open CIL.Safety UInt256Model.Safety UInt256Proof.Transport UInt256Proof.Shift.Safety

/-- The compiled `count >> 6` helper. -/
def countBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], code := [.arg 0, .const32 6, .shr, .ret] }

/-- The left body with its whole-limb count computed by a call to `countBody`. -/
def helperBody (profile : CIL.FeatureProfile) (storage helper : Nat) : CIL.Method :=
  let canonical := scalarBody profile .left storage
  { canonical with code := [.arg 1, .call helper 1] ++ (canonical.code.drop 3).map (relocateOp (· - 1)) }

theorem count_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (countBody profile)) (memory : Memory) (count : BitVec 32) :
    invoke program 4 index [.scalar (.i32 count)] memory =
      .ok (memory, [.scalar (.i32 (count.sshiftRight 6))]) := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have checked : ([.scalar (.i32 count)] : List Value).mapM (checkedValue memory) = .ok [.scalar (.i32 count)] := rfl
  have setup : enterFrame (countBody profile) [.scalar (.i32 count)] memory = .ok (frame, memory) := rfl
  apply invoke_of_run found checked setup
  iterate 3
    apply Eq.trans
    · apply run_next found (by rfl)
      shift_pure_step []
  exact run_return found (by rfl) (by rfl) (by rfl)

/-- A finished canonical run passes through PC 3 with exactly the whole-limb count on the stack. -/
theorem canonical_prefix_strip (profile : CIL.FeatureProfile) (program : CIL.Program) (index storage fuel : Nat)
    (found : program[index]? = some (scalarBody profile .left storage))
    (args : List Value) (frame : Frame) (memory final : Memory) (count : BitVec 32) (returned : List Value)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (finished : run program fuel index 0 args frame [] memory = .ok (final, returned)) :
    ∃ remaining, run program remaining index 3 args frame [.scalar (.i32 (count.sshiftRight 6))] memory =
      .ok (final, returned) := by
  have firstStep : step (scalarBody profile .left storage) (.arg 1) 0 args frame [] memory =
      .ok (.next 1 [.scalar (.i32 count)] frame memory) := by
    simp [step, argument, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have secondStep : step (scalarBody profile .left storage) (.const32 6) 1 args frame [.scalar (.i32 count)] memory =
      .ok (.next 2 [.scalar (.i32 6), .scalar (.i32 count)] frame memory) := by shift_pure_step []
  have thirdStep : step (scalarBody profile .left storage) .shr 2 args frame
      [.scalar (.i32 6), .scalar (.i32 count)] memory =
      .ok (.next 3 [.scalar (.i32 (count.sshiftRight 6))] frame memory) := by shift_pure_step []
  cases fuel with
  | zero => simp [run] at finished
  | succ fuel =>
    rw [run_next found (by rfl) firstStep] at finished
    cases fuel with
    | zero => simp [run] at finished
    | succ fuel =>
      rw [run_next found (by rfl) secondStep] at finished
      cases fuel with
      | zero => simp [run] at finished
      | succ fuel =>
        rw [run_next found (by rfl) thirdStep] at finished
        exact ⟨fuel, finished⟩

theorem helper_prefix_prepend (profile : CIL.FeatureProfile) (program : CIL.Program) (index storage helper : Nat)
    (found : program[index]? = some (helperBody profile storage helper))
    (helperFound : program[helper]? = some (countBody profile))
    (args : List Value) (frame : Frame) (memory final : Memory) (count : BitVec 32) (returned : List Value)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (suffix : ∃ fuel, run program fuel index 2 args frame [.scalar (.i32 (count.sshiftRight 6))] memory =
      .ok (final, returned)) :
    ∃ fuel, run program fuel index 0 args frame [] memory = .ok (final, returned) := by
  have firstStep : step (helperBody profile storage helper) (.arg 1) 0 args frame [] memory =
      .ok (.next 1 [.scalar (.i32 count)] frame memory) := by
    simp [step, argument, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have callStep : step (helperBody profile storage helper) (.call helper 1) 1 args frame
      [.scalar (.i32 count)] memory = .ok (.call helper [.scalar (.i32 count)] [] memory) := rfl
  obtain ⟨fuel, finished⟩ := run_call_exists found (by rfl) callStep
    ⟨4, count_invoke profile program helper helperFound memory count⟩ suffix
  exact ⟨fuel + 1, (run_next found (by rfl) firstStep).trans finished⟩

theorem helper_suffix_lookup (profile : CIL.FeatureProfile) (storage helper pc : Nat) (inside : 3 ≤ pc) :
    (helperBody profile storage helper).code[pc - 1]? =
      ((scalarBody profile .left storage).code[pc]?).map (relocateOp (· - 1)) := by
  change ([CIL.Op.arg 1, .call helper 1] ++
    ((scalarBody profile .left storage).code.drop 3).map (relocateOp (· - 1)))[pc - 1]? = _
  rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.getElem?_map, List.getElem?_drop]
  have index : 3 + (pc - 1 - 2) = pc := by omega
  rw [index]

/-- The helper variant satisfies the public left-shift contract for any call-free storage callee
    whose own contract is supplied; scalar and vector storage instantiate it below. -/
theorem helper_contract (profile : CIL.FeatureProfile) (storageBody : CIL.Method)
    (callFree : CallFree storageBody)
    (storeOf : ∀ program : CIL.Program, ∀ storage, program[storage]? = some storageBody → StoreLimbsContract program storage)
    (program : CIL.Program) (index storage helper : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (helperBody profile storage helper))
    (storageFound : program[storage]? = some storageBody)
    (helperFound : program[helper]? = some (countBody profile)) : ShiftContract .left program index := by
  intro memory input count output call
  let virtual := program.set index (scalarBody profile .left storage)
  have indexBound := (List.getElem?_eq_some_iff.mp found).choose
  have virtualFound : virtual[index]? = some (scalarBody profile .left storage) := List.getElem?_set_self indexBound
  have virtualStorage : virtual[storage]? = some storageBody := by
    simpa only [virtual, List.getElem?_set_ne distinct] using storageFound
  obtain ⟨fuel, final, certificate, value, writable, readable, footprint⟩ :=
    scalar_correctness virtualFound (storeOf virtual storage virtualStorage) memory input count output
      (set_calling (source := scalarBody profile .left storage) found rfl call)
  obtain ⟨_, body, frame, entered, bodyFound, checked, setup, finished, _, _, _⟩ := certificate
  rw [virtualFound] at bodyFound
  cases bodyFound
  obtain ⟨remaining, suffix⟩ := canonical_prefix_strip profile virtual index storage fuel virtualFound
    (shiftArguments input count output) frame entered final count [] (by rfl) finished
  have relation := suffix_correspondence program index storage 3 (· - 1) (scalarBody profile .left storage)
    (helperBody profile storage helper) storageBody distinct found storageFound callFree (fun _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl) (fun pc lower => by omega)
    (fun pc op _ opcode => ⟨left_supported profile storage op (List.mem_of_getElem? opcode),
      left_flow_inputs profile storage op (List.mem_of_getElem? opcode)⟩)
    (fun pc lower => helper_suffix_lookup profile storage helper pc lower)
  have moved := run_success_transport virtual program _ _ relation remaining index 3
    (shiftArguments input count output) frame [.scalar (.i32 (count.sshiftRight 6))] entered final []
    (Or.inr ⟨rfl, Nat.le_refl 3⟩) suffix
  obtain ⟨targetFuel, executed⟩ := helper_prefix_prepend profile program index storage helper found helperFound
    (shiftArguments input count output) frame entered final count [] (by rfl)
    ⟨remaining, by simpa [suffixMap] using moved⟩
  have targetSetup : enterFrame (helperBody profile storage helper) (shiftArguments input count output) memory =
    .ok (frame, entered) := setup
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked targetSetup
  exact ⟨targetFuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked targetSetup live executed,
    value, writable, readable, footprint⟩

theorem scalar_helper_contract (profile : CIL.FeatureProfile) (scalar : profile.vector256Accelerated = false)
    (program : CIL.Program) (index storage helper : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (helperBody profile storage helper))
    (storageFound : program[storage]? = some (UInt256Proof.StorageScalar.body profile))
    (helperFound : program[helper]? = some (countBody profile)) : ShiftContract .left program index :=
  helper_contract profile _ (scalar_storage_call_free profile)
    (fun program storage found => UInt256Proof.StorageScalar.store_limbs_readable_contract profile scalar program storage found)
    program index storage helper distinct found storageFound helperFound

theorem vector_helper_contract (profile : CIL.FeatureProfile) (vector : profile.vector256Accelerated = true)
    (program : CIL.Program) (index storage helper : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (helperBody profile storage helper))
    (storageFound : program[storage]? = some (UInt256Proof.StorageVector.body profile))
    (helperFound : program[helper]? = some (countBody profile)) : ShiftContract .left program index :=
  helper_contract profile _ (vector_storage_call_free profile)
    (fun program storage found => UInt256Proof.StorageVector.store_limbs_readable_contract profile vector program storage found)
    program index storage helper distinct found storageFound helperFound

#print axioms scalar_helper_contract
#print axioms vector_helper_contract
end UInt256Proof.Shift.Variant
