import UInt256.Methods.Add.Vector256Finish
import UInt256.Methods.AddSubtract.CascadeHelper

namespace UInt256Proof.Add.Vector256
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract

/-- `FinishAdd` with the cascade sum computed by a private helper call. -/
def finishAddHelperBody (profile : CIL.FeatureProfile) (lookup accumulate : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.i32 0, .i32 0, .v256 0], localKinds := [.word32, .word32, .vector256], parameterHomes := [], staticSites := [], code := [
  .arg 3,
  .skipInit,
  .arg 1,
  .intrinsic (.vector (.reinterpret 256)) 1,
  .intrinsic (.avx .moveMask64) 1,
  .setLocal 0,
  .arg 2,
  .intrinsic (.vector (.reinterpret 256)) 1,
  .intrinsic (.avx .moveMask64) 1,
  .setLocal 1,
  .local 1,
  .local 0,
  .call accumulate 2,
  .setLocal 0,
  .local 1,
  .local 0,
  .bxor,
  .setLocal 1,
  .local 1,
  .const32 (BitVec.ofInt 32 (15)),
  .band,
  .setLocal 1,
  .call lookup 0,
  .memory .spanReference,
  .memory .asRef,
  .local 1,
  .convU,
  .memory (.add 32 false),
  .memory .load256,
  .setLocal 2,
  .arg 3,
  .memory .asRef,
  .arg 0,
  .local 2,
  .intrinsic (.vector (.add64 256)) 2,
  .memory .store256,
  .local 0,
  .const32 (BitVec.ofInt 32 (16)),
  .band,
  .const32 0,
  .gtu,
  .ret (some .unsigned8)] }

theorem finish_helper_index (program : CIL.Program) (method lookup accumulate : Nat) (profile : CIL.FeatureProfile)
    (avx512 : Bool) (found : program[method]? = some (finishAddHelperBody profile lookup accumulate))
    (accumulateFound : program[accumulate]? = some (accumulateBody profile))
    (features : AddProfile profile avx512)
    (memory entered current : Memory) (output : Reference) (frame : Frame)
    (originalCall : CallingConditions program memory [] [output])
    (homes : WritableHomes entered memory.nextIdentity
      (finishAddHelperBody profile lookup accumulate).localKinds frame.locals)
    (sum carry propagation : BitVec 256)
    (state : VectorFrame program memory entered current [] output frame (fun _ => none) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program memory entered after [] output frame (finishLocals carry propagation) none →
      ∃ fuel final values,
        run program fuel method 22 (finishArguments sum carry propagation output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 0 (finishArguments sum carry propagation output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (finishAddHelperBody profile lookup accumulate).profile = profile := rfl
  finish_pure
  finish_pure
  finish_pure
  finish_pure
  finish_pure
  finish_store
  finish_pure
  finish_pure
  finish_pure
  finish_store
  finish_load
  finish_load
  apply run_pure_call_exists post found (by rfl)
    (by simp [step, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact ⟨⟨rfl, rfl⟩, rfl⟩)
    ⟨6, accumulate_invoke profile program accumulate accumulateFound current _ _⟩
  finish_store
  finish_load
  finish_load
  finish_pure
  finish_store
  finish_load
  finish_pure
  finish_pure
  finish_store
  exact continuation current state

theorem finish_helper_tail (program : CIL.Program) (method lookup accumulate : Nat) (profile : CIL.FeatureProfile)
    (avx512 : Bool) (found : program[method]? = some (finishAddHelperBody profile lookup accumulate))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : AddProfile profile avx512)
    (memory entered current : Memory) (output : Reference) (frame : Frame)
    (originalCall : CallingConditions program memory [] [output])
    (homes : WritableHomes entered memory.nextIdentity
      (finishAddHelperBody profile lookup accumulate).localKinds frame.locals)
    (sum carry propagation : BitVec 256)
    (state : VectorFrame program memory entered current [] output frame (finishLocals carry propagation) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after known,
      VectorFrame program memory entered after [] output frame known (some (finishSum sum carry propagation)) →
      post (leaveFrame frame after) [.scalar (.i32 (finishFlag carry propagation))]) :
    ∃ fuel final values,
      run program fuel method 22 (finishArguments sum carry propagation output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (finishAddHelperBody profile lookup accumulate).profile = profile := rfl
  apply UInt256Proof.AddSubtract.Vector256.run_lookup post state found (by rfl) lookupFound
  intro current reference state loaded formed
  obtain ⟨added, row⟩ := UInt256Proof.AddSubtract.Vector256.table_row current reference state.call.1.1 loaded
    (UInt256Proof.SIMD.cascadeIndex (CIL.Vector.moveMask64 carry) (CIL.Vector.moveMask64 propagation))
    (UInt256Proof.SIMD.cascade_index_bound _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, staticInstruction, memoryInstruction, formValue, formed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simp [step, staticInstruction, memoryInstruction, formValue, formed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  finish_load
  finish_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, staticInstruction, memoryInstruction, referenceAt, CIL.offsetValue, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [added]
  apply run_next_exists post found (by rfl)
  · simp [step, staticInstruction, memoryInstruction, row,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl, rfl, rfl⟩
  finish_store
  finish_pure
  finish_pure
  finish_pure
  finish_load
  finish_pure
  obtain ⟨stored, storeStep, state⟩ := state.output_store originalCall homes
    (finishAddHelperBody profile lookup accumulate) 35 (finishArguments sum carry propagation output) []
    (finishSum sum carry propagation)
  apply run_next_exists post found (by rfl) storeStep
  finish_load
  finish_pure
  finish_pure
  finish_pure
  finish_pure
  have returns : (finishAddHelperBody profile lookup accumulate).returnsValue = true := rfl
  have fetched : (finishAddHelperBody profile lookup accumulate).code[41]? = some (.ret (some .unsigned8)) := rfl
  have normalized : CIL.NarrowKind.unsigned8.extend (finishFlag carry propagation) =
      finishFlag carry propagation := by
    unfold finishFlag
    split <;> rfl
  refine ⟨1, _, _, ?_, continuation stored _ state⟩
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact normalized

/-- `FinishAdd` through the cascade helper keeps the inline body's caller guarantees. -/
theorem finish_helper_contract (program : CIL.Program) (method lookup accumulate : Nat)
    (profile : CIL.FeatureProfile) (avx512 : Bool)
    (found : program[method]? = some (finishAddHelperBody profile lookup accumulate))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (accumulateFound : program[accumulate]? = some (accumulateBody profile))
    (features : AddProfile profile avx512) : FinishContract program method := by
  intro memory output originalCall sum carry propagation
  obtain ⟨frame, entered, setup, numeric, _, _⟩ := numeric_frame_setup
    (finishAddHelperBody profile lookup accumulate) finishSpecs rfl rfl rfl rfl memory
    (finishArguments sum carry propagation output) originalCall.1.1
  have homes : WritableHomes entered memory.nextIdentity
      (finishAddHelperBody profile lookup accumulate).localKinds frame.locals :=
    UInt256Model.Safety.NumericHomes.writable numeric
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
    apply finish_helper_index program method lookup accumulate profile avx512 found accumulateFound features
      memory entered entered output frame originalCall homes sum carry propagation
      (VectorFrame.initial originalCall setup) post
    intro after state
    apply finish_helper_tail program method lookup accumulate profile avx512 found lookupFound features memory
      entered after output frame originalCall homes sum carry propagation state post
    intro after known state
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

#print axioms finish_helper_index
#print axioms finish_helper_tail
#print axioms finish_helper_contract
end UInt256Proof.Add.Vector256
