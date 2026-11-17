import CIL.Safety.LocalSnapshotSteps
import CIL.Safety.Equations
import UInt256.Methods.Add.Vector256Bodies
import UInt256.Safety.ScratchCells
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.StepComposition
import CIL.Safety.NumericHomes
import UInt256.Methods.AddSubtract.BroadcastLookup

namespace UInt256Proof.Add.Vector256
open CIL.Safety UInt256Model.Safety
variable {identity : Nat} {assembly : String}

/-- The extracted profile facts the AVX2 Add bodies depend on. -/
structure AddProfile (profile : CIL.FeatureProfile) (avx512 : Bool) : Prop where
  avx : profile.avx = true
  avx2 : profile.avx2 = true
  wideF : profile.avx512F = avx512
  wide : profile.avx512FVL = avx512

def finishArguments (sum carry propagation : BitVec 256) (output : Reference) : List Value :=
  [.scalar (.v256 sum), .scalar (.v256 carry), .scalar (.v256 propagation), .reference (.address output)]

def finishSpecs : List NumericLocalSpec :=
  [⟨.word32, .i32 0, 0, rfl⟩, ⟨.word32, .i32 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩]

/-- The cascade-corrected sum `FinishAdd` stores. -/
def finishSum (sum carry propagation : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (· + ·) sum (UInt256Proof.SIMD.cascadeVector
    (UInt256Proof.SIMD.cascadeIndex (CIL.Vector.moveMask64 carry) (CIL.Vector.moveMask64 propagation)))

/-- Bit 4 of the cascade sum, the carry out of the top limb. -/
def finishFlag (carry propagation : BitVec 256) : BitVec 32 :=
  if 0#32 < (CIL.Vector.moveMask64 propagation + 2 * CIL.Vector.moveMask64 carry) &&& 16#32 then 1#32 else 0#32

/-- `FinishAdd`: the table-corrected lane sum, the top carry bit, and no other caller byte changed. -/
theorem finish_invoke (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 : Bool) (found : program[method]? = some (finishAddBody profile lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : AddProfile profile avx512)
    (memory : Memory) (output : Reference) (originalCall : CallingConditions program memory [] [output])
    (sum carry propagation : BitVec 256) :
    ∃ fuel after,
      invoke program fuel method (finishArguments sum carry propagation output) memory =
        .ok (after, [.scalar (.i32 (finishFlag carry propagation))]) ∧
      CIL.Safety.read after output 32 1 = .ok (numberBytes (finishSum sum carry propagation).toNat 32) ∧
      access after output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        after.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, setup, numeric, _, _⟩ := numeric_frame_setup
    (finishAddBody profile lookup) finishSpecs rfl rfl rfl rfl rfl memory
    (finishArguments sum carry propagation output) originalCall.1.1
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member =>
    ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (finishFlag carry propagation))] ∧
    CIL.Safety.read final output 32 1 = .ok (numberBytes (finishSum sum carry propagation).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = memory.cells id offset
  have finished : ∃ fuel final returned,
      run program fuel method 0 (finishArguments sum carry propagation output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    have facts {known stored current}
        (state : VectorFrame program memory entered current [] output frame known stored) :
        form current output = .ok output ∧ profile.avx = true ∧ profile.avx2 = true ∧
          (finishAddBody profile lookup).profile = profile :=
      ⟨state.call.output_formed (by simp), features.avx, features.avx2, rfl⟩
    have state := VectorFrame.initial originalCall setup
    obtain ⟨enteredFormed, formed, authority, valid, preserved⟩ :=
      state.walk_facts memory.nextIdentity
    cil_contract_steps (snapshots := state.locals) [found, finishArguments, facts state,
      CIL.FeatureProfile.evaluate]
    replace state := state.after_stores originalCall localSnapshots_4 (remembered :=
      rememberLocal _ 1 (.i32 (UInt256Proof.SIMD.cascadeIndex (CIL.Vector.moveMask64 carry) _)))
    apply UInt256Proof.AddSubtract.Vector256.run_lookup post state found (by rfl) lookupFound
    intro current reference state loaded formed
    obtain ⟨added, row⟩ := UInt256Proof.AddSubtract.Vector256.table_row current reference
      state.call.1.1 loaded _ (UInt256Proof.SIMD.cascade_index_bound
        (CIL.Vector.moveMask64 carry) (CIL.Vector.moveMask64 propagation))
    cil_contract_steps (snapshots := state.locals) [found, finishArguments, facts state,
      CIL.FeatureProfile.evaluate, formed, added, row]
    refine state.run_store post originalCall numeric.complete found fun current state => ?_
    cil_contract_steps (snapshots := state.locals) [found, finishArguments, facts state,
      CIL.FeatureProfile.evaluate]
    refine state.run_output post originalCall numeric.complete found fun current state => ?_
    cil_contract_steps (snapshots := state.locals) [found, finishArguments, facts state,
      CIL.FeatureProfile.evaluate, CIL.NarrowKind.extend_ite_ofNat_one_zero]
    obtain ⟨_, access, footprint⟩ := state.finish originalCall owned
    exact ⟨rfl, state.finish_read originalCall owned, access, footprint⟩
  obtain ⟨fuel, final, returned, ran, flag, value, access, footprint⟩ := finished
  have formedOutput := originalCall.output_formed (reference := output) (by simp)
  have checked : (finishArguments sum carry propagation output).mapM (checkedValue memory) =
      .ok (finishArguments sum carry propagation output) := by
    simp [finishArguments, checkedValue, numericValue, formValue, formedOutput, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  subst flag
  refine ⟨fuel, final, ?_, value, access, footprint⟩
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

/-- What a compiled `FinishAdd` guarantees its caller, independent of its body. -/
def FinishContract (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (output : Reference), CallingConditions program memory [] [output] →
    ∀ sum carry propagation : BitVec 256, ∃ fuel after,
      invoke program fuel method (finishArguments sum carry propagation output) memory =
        .ok (after, [.scalar (.i32 (finishFlag carry propagation))]) ∧
      CIL.Safety.read after output 32 1 = .ok (numberBytes (finishSum sum carry propagation).toNat 32) ∧
      access after output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        after.cells id offset = memory.cells id offset

theorem finish_contract (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 : Bool) (found : program[method]? = some (finishAddBody profile lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : AddProfile profile avx512) : FinishContract program method :=
  fun memory output call sum carry propagation =>
    finish_invoke program method lookup profile avx512 found lookupFound features memory output call sum carry propagation

end UInt256Proof.Add.Vector256
