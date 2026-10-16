import UInt256.Methods.Subtract.Vector256Bodies
import UInt256.Methods.Subtract.Vector256Math
import UInt256.Safety.VectorFrame
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.StepComposition
import UInt256.Methods.AddSubtract.BroadcastLookup

namespace UInt256Proof.Subtract.Vector256
open CIL.Safety UInt256Model.Safety

/-- The extracted profile facts the AVX2 body depends on. -/
structure ImplProfile (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool) : Prop where
  avx : profile.avx = true
  avx2 : profile.avx2 = true
  wideF : profile.avx512F = avx512
  wide : profile.avx512FVL = avx512
  bits : profile.bmi1 = bmi1

/-- Locals 0-2 after loading both operands and forming the lane differences. -/
def differenceLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (rememberLocal (fun _ => none) 0 (.v256 left)) 1 (.v256 right)) 2
    (.v256 (CIL.Vector.zip256 (· - ·) left right))

set_option hygiene false in
/-- One pure instruction of the impl body; expects `post found features profileEq state left right output`. -/
macro "impl_pure" : tactic => `(tactic|
  (have formedLeft := state.call.input_formed (reference := left) (by simp)
   have formedRight := state.call.input_formed (reference := right) (by simp)
   have formedOutput := state.call.output_formed (reference := output) (by simp)
   apply run_next_exists post found (by rfl)
   · simp (config := { implicitDefEqProofs := false })
       [step, pureArity, binaryArguments, checkedValue, numericValue, formValue, formedLeft, formedRight,
         formedOutput, staticInstruction, memoryInstruction, checkedAt, profileEq, features.avx, features.avx2,
         features.wideF, features.wide, features.bits, CIL.FeatureProfile.evaluate, scalars, checkedIntrinsic,
         CIL.Intrinsic.available, CIL.step.eq_def, CIL.binary, CIL.unary, CIL.truth, instruction,
         Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
     try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

set_option hygiene false in
/-- Store the top of stack in a typed local; expects `post state originalCall homes found`. -/
macro "impl_store" : tactic => `(tactic|
  (apply VectorFrame.run_store post state originalCall homes found (by rfl) (by rfl) (by rfl) (by rfl)
   intro current state))

set_option hygiene false in
macro "impl_load" : tactic => `(tactic|
  apply VectorFrame.run_load post state found (by rfl) (by rfl))

theorem impl_inputs (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (state : VectorFrame program original entered current [left, right] output frame (fun _ => none) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame
        (differenceLocals (inputValue original left) (inputValue original right)) none →
      ∃ fuel final values,
        run program fuel method 14 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 0 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : left ∈ [left, right])
  have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input current left
  have sameLeft := state.input_value originalCall (by simp : left ∈ [left, right])
  rw [sameLeft] at castLeft
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

/-- Locals 0-4 after the borrow mask and its incoming shift. -/
def maskLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (differenceLocals left right) 3 (.v256 (borrowLanes left right))) 4
    (.v256 (borrowIncoming (borrowLanes left right)))

theorem impl_masks (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (differenceLocals a b) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame (maskLocals a b) none →
      ∃ fuel final values,
        run program fuel method 50 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 14 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  cases avx512
  · impl_pure
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

/-- The first output store writes the speculative difference. -/
def speculative (left right : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (· + ·) (CIL.Vector.zip256 (· - ·) left right) (borrowIncoming (borrowLanes left right))

def equalLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  rememberLocal (maskLocals left right) 5 (.v256 (equalLanes left right))

theorem impl_decision (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (maskLocals a b) none)
    (post : Memory → List Value → Prop)
    (fast : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0 → ∀ after,
      VectorFrame program original entered after [left, right] output frame (equalLocals a b)
        (some (speculative a b)) →
      ∃ fuel final values,
        run program fuel method 117 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values)
    (slow : equalLanes a b &&& borrowIncoming (borrowLanes a b) ≠ 0 → ∀ after,
      VectorFrame program original entered after [left, right] output frame (equalLocals a b)
        (some (speculative a b)) →
      ∃ fuel final values,
        run program fuel method 66 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 50 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  impl_load
  impl_load
  impl_pure
  obtain ⟨stored, storeStep, state⟩ := state.output_store originalCall homes
    (subtractImplBody profile avx512 bmi1 lookup) 57 (binaryArguments left right output) []
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
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (pc : Nat) (fetched : (subtractImplBody profile avx512 bmi1 lookup).code[pc]? = some (.ret (some .unsigned8)))
    (args : List Value) (frame : Frame) (memory : Memory) (flag : BitVec 32)
    (normalized : CIL.NarrowKind.unsigned8.extend flag = flag) :
    run program 1 method pc args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have returns : (subtractImplBody profile avx512 bmi1 lookup).returnsValue = true := rfl
  simp [run, found, fetched, returns, step, normalized, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem impl_fast_return (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (equalLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : post (leaveFrame frame current)
      [.scalar (.i32 (if 0#32 < CIL.Vector.moveMask64 (borrowLanes a b) &&& 8#32 then 1#32 else 0#32))]) :
    ∃ fuel final values,
      run program fuel method 117 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractImplBody profile avx512 bmi1 lookup).profile = profile := rfl
  impl_load
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  impl_pure
  exact ⟨1, _, _, impl_return program method lookup profile avx512 bmi1 found 124 rfl _ frame current _
    (by split <;> rfl), continuation⟩

#print axioms impl_return
#print axioms impl_fast_return

/-- Locals after forming the cascade sum and table index from the two lane masks. -/
def slowLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  let g := CIL.Vector.moveMask64 (borrowLanes left right)
  let p := CIL.Vector.moveMask64 (equalLanes left right)
  rememberLocal (rememberLocal (rememberLocal (rememberLocal (rememberLocal (equalLocals left right)
    6 (.i32 g)) 7 (.i32 p)) 6 (.i32 (p + 2 * g))) 7 (.i32 (p ^^^ (p + 2 * g)))) 7
    (.i32 (UInt256Proof.SIMD.cascadeIndex g p))

theorem impl_index (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (equalLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame (slowLocals a b) (some value) →
      ∃ fuel final values,
        run program fuel method 88 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 66 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractImplBody profile avx512 bmi1 lookup).profile = profile := rfl
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

theorem bextr_bit (x : BitVec 32) :
    (((CIL.Vector.bextr32 x 4 1).setWidth 8).setWidth 32).toNat ≤ 1 := by
  simp [CIL.Vector.bextr32]
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))

/-- The corrected difference after the table lookup. -/
def corrected (left right : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (· - ·) (CIL.Vector.zip256 (· - ·) left right)
    (UInt256Proof.SIMD.cascadeVector (UInt256Proof.SIMD.cascadeIndex
      (CIL.Vector.moveMask64 (borrowLanes left right)) (CIL.Vector.moveMask64 (equalLanes left right))))

theorem impl_slow_tail (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : WritableHomes entered original.nextIdentity
      (subtractImplBody profile avx512 bmi1 lookup).localKinds frame.locals)
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
      run program fuel method 88 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractImplBody profile avx512 bmi1 lookup).profile = profile := rfl
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
    (subtractImplBody profile avx512 bmi1 lookup) 101 (binaryArguments left right output) []
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
    exact ⟨1, _, _, impl_return program method lookup profile _ false found 109 rfl _ frame stored _
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
    exact ⟨1, _, _, impl_return program method lookup profile _ true found 116 rfl _ frame stored _
      (by simp [CIL.NarrowKind.extend]), continuation stored state⟩

end UInt256Proof.Subtract.Vector256
