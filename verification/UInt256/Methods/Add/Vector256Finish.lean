import UInt256.Methods.Add.Vector256Bodies
import UInt256.Safety.ScratchCells
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.StepComposition
import CIL.Safety.NumericHomes
import UInt256.Methods.AddSubtract.BroadcastLookup

namespace UInt256Proof.Add.Vector256
open CIL.Safety UInt256Model.Safety

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

/-- Locals after the two lane masks, the cascade sum and the table index. -/
def finishLocals (carry propagation : BitVec 256) : Nat → Option CIL.Value :=
  let g := CIL.Vector.moveMask64 carry
  let p := CIL.Vector.moveMask64 propagation
  rememberLocal (rememberLocal (rememberLocal (rememberLocal (rememberLocal (fun _ => none)
    0 (.i32 g)) 1 (.i32 p)) 0 (.i32 (p + 2 * g))) 1 (.i32 (p ^^^ (p + 2 * g)))) 1
    (.i32 (UInt256Proof.SIMD.cascadeIndex g p))

set_option hygiene false in
/-- One pure instruction of `FinishAdd`; expects `post found features profileEq state output`. -/
macro "finish_pure" : tactic => `(tactic|
  (have formedOutput := state.call.output_formed (reference := output) (by simp)
   apply run_next_exists post found (by rfl)
   · simp (config := { implicitDefEqProofs := false })
       [step, pureArity, finishArguments, checkedValue, numericValue, formValue, formedOutput,
         staticInstruction, memoryInstruction, checkedAt, profileEq, features.avx, features.avx2,
         CIL.FeatureProfile.evaluate, scalars, checkedIntrinsic, CIL.Intrinsic.available, CIL.step.eq_def,
         CIL.binary, CIL.unary, CIL.truth, instruction, Except.mapError, Bind.bind, Except.bind, Pure.pure,
         Except.pure]
     try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

set_option hygiene false in
macro "finish_store" : tactic => `(tactic|
  (apply VectorFrame.run_store post state originalCall homes found (by rfl) (by rfl) (by rfl) (by rfl)
   intro current state))

set_option hygiene false in
macro "finish_load" : tactic => `(tactic|
  apply VectorFrame.run_load post state found (by rfl) (by rfl))

theorem finish_index (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 : Bool) (found : program[method]? = some (finishAddBody profile lookup))
    (features : AddProfile profile avx512)
    (memory entered current : Memory) (output : Reference) (frame : Frame)
    (originalCall : CallingConditions program memory [] [output])
    (homes : WritableHomes entered memory.nextIdentity (finishAddBody profile lookup).localKinds frame.locals)
    (sum carry propagation : BitVec 256)
    (state : VectorFrame program memory entered current [] output frame (fun _ => none) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program memory entered after [] output frame (finishLocals carry propagation) none →
      ∃ fuel final values,
        run program fuel method 24 (finishArguments sum carry propagation output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 0 (finishArguments sum carry propagation output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (finishAddBody profile lookup).profile = profile := rfl
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
  finish_pure
  finish_load
  finish_pure
  finish_pure
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

theorem finish_tail (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 : Bool) (found : program[method]? = some (finishAddBody profile lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : AddProfile profile avx512)
    (memory entered current : Memory) (output : Reference) (frame : Frame)
    (originalCall : CallingConditions program memory [] [output])
    (homes : WritableHomes entered memory.nextIdentity (finishAddBody profile lookup).localKinds frame.locals)
    (sum carry propagation : BitVec 256)
    (state : VectorFrame program memory entered current [] output frame (finishLocals carry propagation) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after known,
      VectorFrame program memory entered after [] output frame known (some (finishSum sum carry propagation)) →
      post (leaveFrame frame after) [.scalar (.i32 (finishFlag carry propagation))]) :
    ∃ fuel final values,
      run program fuel method 24 (finishArguments sum carry propagation output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (finishAddBody profile lookup).profile = profile := rfl
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
    (finishAddBody profile lookup) 37 (finishArguments sum carry propagation output) []
    (finishSum sum carry propagation)
  apply run_next_exists post found (by rfl) storeStep
  finish_load
  finish_pure
  finish_pure
  finish_pure
  finish_pure
  have returns : (finishAddBody profile lookup).returnsValue = true := rfl
  have fetched : (finishAddBody profile lookup).code[43]? = some (.ret (some .unsigned8)) := rfl
  have normalized : CIL.NarrowKind.unsigned8.extend (finishFlag carry propagation) =
      finishFlag carry propagation := by
    unfold finishFlag
    split <;> rfl
  refine ⟨1, _, _, ?_, continuation stored _ state⟩
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact normalized

/-- `FinishAdd`: the table-corrected lane sum, the top carry bit, and no other caller byte changed. -/
theorem finish_invoke (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 : Bool) (found : program[method]? = some (finishAddBody profile lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
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
    (finishAddBody profile lookup) finishSpecs rfl rfl rfl rfl memory
    (finishArguments sum carry propagation output) originalCall.1.1
  have homes : WritableHomes entered memory.nextIdentity
      (finishAddBody profile lookup).localKinds frame.locals :=
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
    apply finish_index program method lookup profile avx512 found features memory entered entered output frame
      originalCall homes sum carry propagation (VectorFrame.initial originalCall setup) post
    intro after state
    apply finish_tail program method lookup profile avx512 found lookupFound features memory entered after
      output frame originalCall homes sum carry propagation state post
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
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : AddProfile profile avx512) : FinishContract program method :=
  fun memory output call sum carry propagation =>
    finish_invoke program method lookup profile avx512 found lookupFound features memory output call sum carry propagation

#print axioms finish_index
#print axioms finish_tail
#print axioms finish_invoke
#print axioms finish_contract
end UInt256Proof.Add.Vector256
