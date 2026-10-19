import UInt256.Methods.Subtract.Vector256Contract
import UInt256.Safety.ReportingForwarder

namespace UInt256Proof.Subtract.Vector256.Guarded
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Vector256

/-- `SubtractImpl` with each feature test written as a conjunction with an implied feature. -/
def subtractGuardImplBody (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool) (lookup : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.v256 0, .v256 0, .v256 0, .v256 0, .v256 0, .v256 0, .i32 0, .i32 0, .v256 0], localKinds := [.vector256, .vector256, .vector256, .vector256, .vector256, .vector256, .word32, .word32, .vector256], parameterHomes := [], staticSites := [], code := [
  .feature .avx2,
  .feature .avx2,
  .band,
  .brzero 129,
  .arg 0,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .setLocal 0,
  .arg 1,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .setLocal 1,
  .local 0,
  .local 1,
  .intrinsic (.vector (.sub64 256)) 2,
  .setLocal 2,
  .feature .avx512FVL,
  .feature .avx,
  .band,
  .brzero 36,
  (if avx512 then .local 0 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .local 1 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .local 2 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .const32 (BitVec.ofInt 32 (142)) else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.avx512 .ternaryLogic) 4 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .const32 (BitVec.ofInt 32 (63)) else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.ashr64 256)) 2 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .setLocal 3 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .local 3 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.vector (.zero 256)) 0 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .const32 3 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .intrinsic (.avx512 .alignRight64) 3 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .setLocal 4 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .branch 54 else .unsupported "Unreachable under selected profile"),
  (if avx512 then .unsupported "Unreachable under selected profile" else .local 0),
  (if avx512 then .unsupported "Unreachable under selected profile" else .local 1),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.vector (.ltu64 256)) 2),
  (if avx512 then .unsupported "Unreachable under selected profile" else .setLocal 3),
  (if avx512 then .unsupported "Unreachable under selected profile" else .local 3),
  (if avx512 then .unsupported "Unreachable under selected profile" else .const32 (BitVec.ofInt 32 (144))),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.avx2 .permute4x64) 2),
  (if avx512 then .unsupported "Unreachable under selected profile" else .const32 0),
  (if avx512 then .unsupported "Unreachable under selected profile" else .convI8),
  (if avx512 then .unsupported "Unreachable under selected profile" else .const32 (BitVec.ofInt 32 (-1))),
  (if avx512 then .unsupported "Unreachable under selected profile" else .convI8),
  (if avx512 then .unsupported "Unreachable under selected profile" else .const32 (BitVec.ofInt 32 (-1))),
  (if avx512 then .unsupported "Unreachable under selected profile" else .convI8),
  (if avx512 then .unsupported "Unreachable under selected profile" else .const32 (BitVec.ofInt 32 (-1))),
  (if avx512 then .unsupported "Unreachable under selected profile" else .convI8),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.vector (.create64 256)) 4),
  (if avx512 then .unsupported "Unreachable under selected profile" else .intrinsic (.vector (.band 256)) 2),
  (if avx512 then .unsupported "Unreachable under selected profile" else .setLocal 4),
  .arg 2,
  .skipInit,
  .arg 2,
  .memory .asRef,
  .local 2,
  .local 4,
  .intrinsic (.vector (.add64 256)) 2,
  .memory .store256,
  .local 0,
  .local 1,
  .intrinsic (.vector (.eq64 256)) 2,
  .setLocal 5,
  .local 5,
  .local 4,
  .intrinsic (.avx .testZ64) 2,
  .brnonzero 121,
  .local 3,
  .intrinsic (.vector (.reinterpret 256)) 1,
  .intrinsic (.avx .moveMask64) 1,
  .setLocal 6,
  .local 5,
  .intrinsic (.vector (.reinterpret 256)) 1,
  .intrinsic (.avx .moveMask64) 1,
  .setLocal 7,
  .local 7,
  .const32 2,
  .local 6,
  .mul,
  .add,
  .setLocal 6,
  .local 7,
  .local 6,
  .bxor,
  .setLocal 7,
  .local 7,
  .const32 (BitVec.ofInt 32 (15)),
  .band,
  .setLocal 7,
  .call lookup 0,
  .memory .spanReference,
  .memory .asRef,
  .local 7,
  .convU,
  .memory (.add 32 false),
  .memory .load256,
  .setLocal 8,
  .arg 2,
  .memory .asRef,
  .local 2,
  .local 8,
  .intrinsic (.vector (.sub64 256)) 2,
  .memory .store256,
  .feature .bmi1,
  .brnonzero 114,
  (if bmi1 then .unsupported "Unreachable under selected profile" else .local 6),
  (if bmi1 then .unsupported "Unreachable under selected profile" else .const32 (BitVec.ofInt 32 (16))),
  (if bmi1 then .unsupported "Unreachable under selected profile" else .band),
  (if bmi1 then .unsupported "Unreachable under selected profile" else .const32 0),
  (if bmi1 then .unsupported "Unreachable under selected profile" else .gtu),
  (if bmi1 then .unsupported "Unreachable under selected profile" else .ret (some .unsigned8)),
  (if bmi1 then .local 6 else .unsupported "Unreachable under selected profile"),
  (if bmi1 then .const32 4 else .unsupported "Unreachable under selected profile"),
  (if bmi1 then .const32 1 else .unsupported "Unreachable under selected profile"),
  (if bmi1 then .intrinsic (.bmi1 .bextr32) 3 else .unsupported "Unreachable under selected profile"),
  (if bmi1 then .convU1 else .unsupported "Unreachable under selected profile"),
  (if bmi1 then .memory .bitcastByteBool else .unsupported "Unreachable under selected profile"),
  (if bmi1 then .ret (some .unsigned8) else .unsupported "Unreachable under selected profile"),
  .local 3,
  .intrinsic (.vector (.reinterpret 256)) 1,
  .intrinsic (.avx .moveMask64) 1,
  .const32 8,
  .band,
  .const32 0,
  .gtu,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

theorem impl_inputs (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractGuardImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (state : VectorFrame program original entered current [left, right] output frame (fun _ => none) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame
        (differenceLocals (inputValue original left) (inputValue original right)) none →
      ∃ fuel final values,
        run program fuel method 16 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 0 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractGuardImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : left ∈ [left, right])
  have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input current left
  have sameLeft := state.input_value originalCall (by simp : left ∈ [left, right])
  rw [sameLeft] at castLeft
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, pureArity, loadLeft]; rfl
  apply run_next_exists post found (by rfl)
  · simp only [step, staticInstruction, castLeft]; rfl
  impl_store
  have loadRight := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : right ∈ [left, right])
  have castRight := UInt256Proof.Equality.VectorPrimitive.cast_input current right
  have sameRight := state.input_value originalCall (by simp : right ∈ [left, right])
  rw [sameRight] at castRight
  impl_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, pureArity, loadRight]; rfl
  apply run_next_exists post found (by rfl)
  · simp only [step, staticInstruction, castRight]; rfl
  impl_store
  impl_load
  impl_load
  impl_pure
  impl_store
  exact continuation current state

#print axioms impl_inputs

theorem impl_masks (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractGuardImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (differenceLocals a b) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame (maskLocals a b) none →
      ∃ fuel final values,
        run program fuel method 54 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 16 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractGuardImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  cases avx512
  · impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_load
    impl_load
    impl_pure
    impl_store
    impl_load
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    rw [show CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (BitVec.ult x y)) a b = borrowLanes a b from rfl,
      permute_incoming]
    impl_store
    exact continuation current state
  · impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_load
    impl_load
    impl_load
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    rw [ternary_borrow_lanes]
    impl_store
    impl_load
    impl_pure
    impl_pure
    impl_pure
    rw [align_incoming]
    impl_store
    impl_pure
    exact continuation current state

#print axioms impl_masks

theorem impl_decision (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractGuardImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (maskLocals a b) none)
    (post : Memory → List Value → Prop)
    (fast : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0 → ∀ after,
      VectorFrame program original entered after [left, right] output frame (equalLocals a b)
        (some (speculative a b)) →
      ∃ fuel final values,
        run program fuel method 121 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values)
    (slow : equalLanes a b &&& borrowIncoming (borrowLanes a b) ≠ 0 → ∀ after,
      VectorFrame program original entered after [left, right] output frame (equalLocals a b)
        (some (speculative a b)) →
      ∃ fuel final values,
        run program fuel method 70 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 54 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractGuardImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  impl_load
  impl_load
  impl_pure
  obtain ⟨stored, storeStep, state⟩ := state.output_store originalCall homes
    (subtractGuardImplBody profile avx512 bmi1 lookup) 61 (binaryArguments left right output) []
    (speculative a b)
  apply run_next_exists post found (by rfl) storeStep
  impl_load
  impl_load
  impl_pure
  impl_store
  impl_load
  impl_load
  impl_pure
  by_cases decided : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0
  · have selected : CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) a b &&&
        borrowIncoming (borrowLanes a b) = 0#256 := decided
    simp only [selected, ite_true]
    impl_pure
    exact fast decided current state
  · have selected : ¬ CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) a b &&&
        borrowIncoming (borrowLanes a b) = 0#256 := decided
    simp only [selected, ite_false]
    impl_pure
    exact slow decided current state

#print axioms impl_decision

/-- The byte return keeps a 0/1 flag. -/
theorem impl_return (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (pc : Nat) (fetched : (subtractGuardImplBody profile avx512 bmi1 lookup).code[pc]? = some (.ret (some .unsigned8)))
    (args : List Value) (frame : Frame) (memory : Memory) (flag : BitVec 32)
    (normalized : CIL.NarrowKind.unsigned8.extend flag = flag) :
    run program 1 method pc args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have returns : (subtractGuardImplBody profile avx512 bmi1 lookup).returnsValue = true := rfl
  simp [run, found, fetched, returns, step, normalized, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem impl_fast_return (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (equalLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : post (leaveFrame frame current)
      [.scalar (.i32 (if 0#32 < CIL.Vector.moveMask64 (borrowLanes a b) &&& 8#32 then 1#32 else 0#32))]) :
    ∃ fuel final values,
      run program fuel method 121 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractGuardImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  impl_load
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  exact ⟨1, _, _, impl_return program method lookup profile avx512 bmi1 found 128 rfl _ frame current _
    (by split <;> rfl), continuation⟩

#print axioms impl_return
#print axioms impl_fast_return

theorem impl_index (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractGuardImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (equalLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame (slowLocals a b) (some value) →
      ∃ fuel final values,
        run program fuel method 92 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 70 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractGuardImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  impl_load
  impl_pure
  impl_pure
  impl_store
  impl_load
  impl_pure
  impl_pure
  impl_store
  impl_load
  impl_pure
  impl_load
  impl_pure
  impl_pure
  impl_store
  impl_load
  impl_load
  impl_pure
  impl_store
  impl_load
  impl_pure
  impl_pure
  impl_store
  exact continuation current state

#print axioms impl_index

theorem impl_slow_tail (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractGuardImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (slowLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame
        (rememberLocal (slowLocals a b) 8 (.v256 (UInt256Proof.SIMD.cascadeVector (UInt256Proof.SIMD.cascadeIndex
          (CIL.Vector.moveMask64 (borrowLanes a b)) (CIL.Vector.moveMask64 (equalLanes a b))))))
        (some (corrected a b)) →
      post (leaveFrame frame after) [.scalar (.i32 (slowFlag bmi1
        (CIL.Vector.moveMask64 (equalLanes a b) + 2 * CIL.Vector.moveMask64 (borrowLanes a b))))]) :
    ∃ fuel final values,
      run program fuel method 92 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractGuardImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  apply UInt256Proof.AddSubtract.Vector256.run_lookup post state found (by rfl) lookupFound
  intro current reference state loaded formed
  obtain ⟨added, row⟩ := UInt256Proof.AddSubtract.Vector256.table_row current reference state.call.1.1 loaded
    (UInt256Proof.SIMD.cascadeIndex (CIL.Vector.moveMask64 (borrowLanes a b)) (CIL.Vector.moveMask64 (equalLanes a b)))
    (UInt256Proof.SIMD.cascade_index_bound _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, staticInstruction, memoryInstruction, formValue, formed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simp [step, staticInstruction, memoryInstruction, formValue, formed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  impl_load
  impl_pure
  apply run_next_exists post found (by rfl)
  · simp only [step, staticInstruction, memoryInstruction, referenceAt, CIL.offsetValue, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [added]
  apply run_next_exists post found (by rfl)
  · simp [step, staticInstruction, memoryInstruction, row,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl, rfl, rfl⟩
  impl_store
  impl_pure
  impl_pure
  impl_load
  impl_load
  impl_pure
  obtain ⟨stored, storeStep, state⟩ := state.output_store originalCall homes
    (subtractGuardImplBody profile avx512 bmi1 lookup) 105 (binaryArguments left right output) []
    (corrected a b)
  apply run_next_exists post found (by rfl) storeStep
  cases bmi1
  · impl_pure
    impl_pure
    impl_load
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    exact ⟨1, _, _, impl_return program method lookup profile _ false found 113 rfl _ frame stored _
      (by split <;> rfl), continuation stored state⟩
  · impl_pure
    impl_pure
    impl_load
    impl_pure
    impl_pure
    impl_pure
    impl_pure
    have bit := bextr_bit (CIL.Vector.moveMask64 (equalLanes a b) + 2#32 * CIL.Vector.moveMask64 (borrowLanes a b))
    simp only [BitVec.toNat_setWidth] at bit
    apply run_next_exists post found (by rfl)
    · simp [step, staticInstruction, memoryInstruction, bit,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨1, _, _, impl_return program method lookup profile _ true found 120 rfl _ frame stored _
      (by simp [CIL.NarrowKind.extend]), continuation stored state⟩

/-- Guarded `SubtractImpl`: the exact initial-operand borrow, the wrapped difference, a writable output and
    unchanged caller bytes outside it, for either borrow-mask form and either flag extraction. -/
theorem impl_contract (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractGuardImplBody profile avx512 bmi1 lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program method := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds
    (body := subtractGuardImplBody profile avx512 bmi1 lookup)
    (by simp [subtractGuardImplBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit,
      ParameterArgumentsFit])
  obtain ⟨frame', entered', setup', homes, _, wf⟩ := numeric_frame_setup
    (subtractGuardImplBody profile avx512 bmi1 lookup) implSpecs rfl rfl rfl rfl memory
    (binaryArguments left right output) call.1.1
  rw [setup] at setup'
  cases setup'
  have writable : WritableHomes entered memory.nextIdentity
      (subtractGuardImplBody profile avx512 bmi1 lookup).localKinds frame.locals :=
    UInt256Model.Safety.NumericHomes.writable homes
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member =>
    ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  have state := VectorFrame.initial call setup
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (inputValue memory left).toNat < (inputValue memory right).toNat
      then 1 else 0))] ∧
    inputValue final output = inputValue memory left - inputValue memory right ∧
    access final output 32 1 true = .ok () ∧
    ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = memory.cells id offset
  have finished : ∃ fuel final returned,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply impl_inputs program method lookup profile avx512 bmi1 found features memory entered entered
      left right output frame call writable state post
    intro after state
    apply impl_masks program method lookup profile avx512 bmi1 found features memory entered after
      left right output frame call writable _ _ state post
    intro after state
    apply impl_decision program method lookup profile avx512 bmi1 found features memory entered after
      left right output frame call writable _ _ state post
    · intro fast after state
      apply impl_fast_return program method lookup profile avx512 bmi1 found features memory entered after
        left right output frame _ _ _ state post
      obtain ⟨value, access, footprint⟩ := state.finish call owned
      exact ⟨by rw [fast_flag_bits _ _ fast]; rfl, value.trans (speculative_value _ _ fast), access, footprint⟩
    · intro _ after state
      apply impl_index program method lookup profile avx512 bmi1 found features memory entered after
        left right output frame call writable _ _ _ state post
      intro after state
      apply impl_slow_tail program method lookup profile avx512 bmi1 found lookupFound features memory entered
        after left right output frame call writable _ _ _ state post
      intro after state
      obtain ⟨value, access, footprint⟩ := state.finish call owned
      exact ⟨by rw [slow_flag_bits]; rfl, value.trans (corrected_value _ _), access, footprint⟩
  obtain ⟨fuel, final, returned, ran, flag, value, access, footprint⟩ := finished
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  subst flag
  refine ⟨fuel, final, ?_, value, access, footprint⟩
  simpa only [decide_eq_true_eq] using
    certify_invocation program method _ _ memory frame entered fuel final _ found checked setup live ran

#print axioms impl_contract

/-- Guarded AVX2 `Subtract`: wrapped difference of the initial operands; the borrow flag is discarded. -/
theorem subtract_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool)
    (entryFound : program[0]? = some (subtractEntryBody profile 1))
    (implFound : program[1]? = some (subtractGuardImplBody profile avx512 bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1) :
    WrappingBinaryContract (· - ·) program 0 :=
  forward_reporting_pop program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile avx512 bmi1 implFound lookupFound features)

/-- Guarded AVX2 `SubtractUnderflow`: wrapped difference and the exact initial-operand borrow. -/
theorem subtract_underflow_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool)
    (entryFound : program[0]? = some (subtractUnderflowEntryBody profile 1))
    (implFound : program[1]? = some (subtractGuardImplBody profile avx512 bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program 0 :=
  forward_reporting_byte program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile avx512 bmi1 implFound lookupFound features)

#print axioms subtract_contract
#print axioms subtract_underflow_contract
end UInt256Proof.Subtract.Vector256.Guarded
