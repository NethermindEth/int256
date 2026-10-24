import UInt256.Methods.Shift.ScalarContract
import UInt256.Methods.Shift.LeftFlow
import UInt256.Methods.StorageFlow
import CIL.Safety.RegionRun
import CIL.Safety.Embedding.Suffix

namespace UInt256Proof.Shift.Variant
open CIL.Safety UInt256Model.Safety UInt256Proof.Transport UInt256Proof.Shift.Safety

/-- The compiled `count >> 6` helper. -/
def countBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], code := [.arg 0, .const32 6, .shr, .ret] }

/-- The left body with its whole-limb count computed by a call to `countBody`. -/
def helperBody (profile : CIL.FeatureProfile) (storage helper : Nat) : CIL.Method :=
  let canonical := scalarBody profile .left storage
  { canonical with code := [.arg 1, .call helper 1] ++ (canonical.code.drop 3).map (CIL.Op.relabel (· - 3 + 2)) }

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
    simp [step, cil_guard, observerCount, argument, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
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
    simp [step, cil_guard, observerCount, argument, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have callStep : step (helperBody profile storage helper) (.call helper 1) 1 args frame
      [.scalar (.i32 count)] memory = .ok (.call helper [.scalar (.i32 count)] [] memory) := rfl
  obtain ⟨fuel, finished⟩ := run_call_exists found (by rfl) callStep
    ⟨4, count_invoke profile program helper helperFound memory count⟩ suffix
  exact ⟨fuel + 1, (run_next found (by rfl) firstStep).trans finished⟩

/-- A replaced method with the same static sites keeps the caller's static-world condition. -/
theorem set_calling {program : CIL.Program} {index : Nat} {source target : CIL.Method}
    (found : program[index]? = some target) (same : source.staticSites = target.staticSites)
    {memory : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) :
    CallingConditions (program.set index source) memory inputs outputs := by
  refine ⟨call.1, ?_⟩
  rw [programStaticDescriptors_set program index source fun old present => by
    rw [found] at present; cases present; rw [same]]
  exact call.2

/-- The canonical body with its count prefix masked; only the suffix from PC 3 is ever run. -/
def suffixBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method :=
  let canonical := scalarBody profile .left storage
  { canonical with code := List.replicate 3 (.unsupported "Outside the region") ++ canonical.code.drop 3 }

/-- The masked suffix runs one PC earlier in the helper variant, after its two-instruction call prefix. -/
theorem suffix_refines (profile : CIL.FeatureProfile) (storage helper : Nat) :
    CIL.Embedding.BodyRefines (suffixBody profile storage) (helperBody profile storage helper)
      (CIL.Embedding.suffixRename 3 2) := by
  have targets : ∀ op ∈ (suffixBody profile storage).code.drop 3, ∀ target ∈ op.targets, 3 ≤ target := by
    intro op member
    simp only [suffixBody, List.drop_append, List.length_replicate, Nat.sub_self, List.drop_zero,
      List.drop_replicate, List.replicate_zero, List.nil_append] at member
    exact (left_flow profile storage op (List.mem_of_mem_drop member)).1
  refine CIL.Embedding.BodyRefines.of_relocated_suffix (lower := 3) (start := 2) ?_ rfl (by omega) ?_ ?_ targets ?_
  · rfl
  · intro pc op before fetched
    rw [suffixBody, List.getElem?_append_left (by simpa only [List.length_replicate] using before),
      List.getElem?_replicate_of_lt before] at fetched
    cases fetched
    rfl
  · simp [helperBody, suffixBody]
  · intro pc after
    rfl

/-- The helper variant satisfies the public left-shift contract for any call-free storage callee
    whose own contract is supplied; scalar and vector storage instantiate it below. -/
theorem helper_contract (profile : CIL.FeatureProfile) (storageBody : CIL.Method)
    (storageCalls : ∀ op ∈ storageBody.code, op.callees = [])
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
  let region : Nat → Nat → Prop := fun method pc => method = storage ∨ method = index ∧ 3 ≤ pc
  have closed : RegionClosed virtual region := by
    intro method pc body op inside fetched opcode
    rcases inside with rfl | ⟨rfl, lower⟩
    · rw [virtualStorage] at fetched
      cases fetched
      have none := storageCalls op (List.mem_of_getElem? opcode)
      exact ⟨fun _ => .inl rfl, fun _ _ => .inl rfl, by simp [none]⟩
    · rw [virtualFound] at fetched
      cases fetched
      obtain ⟨targets, callees⟩ := left_flow profile storage op (List.mem_of_getElem? opcode)
      exact ⟨fun _ => .inr ⟨rfl, by omega⟩, fun target member => .inr ⟨rfl, targets target member⟩,
        fun callee member => .inl (callees callee member)⟩
  have agrees := AgreesOn.set (region := region) virtualFound (suffixBody profile storage).code fun pc inside =>
    code_agrees_of_drop (lower := 3) (by simp [suffixBody])
      (by rcases inside with same | ⟨_, lower⟩; exact absurd same distinct; exact lower)
  have masked := (run_congr_region closed agrees remaining index 3 _ frame _ entered (.inr ⟨rfl, Nat.le_refl 3⟩)).trans
    suffix
  rw [List.set_set] at masked
  have moved := run_refines ((ProgramRefines.refl program).set_body found (suffix_refines profile storage helper))
    remaining index 3 _ frame _ entered _ masked
  obtain ⟨targetFuel, executed⟩ := helper_prefix_prepend profile program index storage helper found helperFound
    (shiftArguments input count output) frame entered final count [] (by rfl)
    ⟨remaining, by simpa [CIL.Embedding.suffixRename] using moved⟩
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
  helper_contract profile _ (scalar_storage_calls_nothing profile)
    (fun program storage found => UInt256Proof.StorageScalar.store_limbs_readable_contract profile scalar program storage found)
    program index storage helper distinct found storageFound helperFound

theorem vector_helper_contract (profile : CIL.FeatureProfile) (vector : profile.vector256Accelerated = true)
    (program : CIL.Program) (index storage helper : Nat) (distinct : index ≠ storage)
    (found : program[index]? = some (helperBody profile storage helper))
    (storageFound : program[storage]? = some (UInt256Proof.StorageVector.body profile))
    (helperFound : program[helper]? = some (countBody profile)) : ShiftContract .left program index :=
  helper_contract profile _ (vector_storage_calls_nothing profile)
    (fun program storage found => UInt256Proof.StorageVector.store_limbs_readable_contract profile vector program storage found)
    program index storage helper distinct found storageFound helperFound

#print axioms scalar_helper_contract
#print axioms vector_helper_contract
end UInt256Proof.Shift.Variant
