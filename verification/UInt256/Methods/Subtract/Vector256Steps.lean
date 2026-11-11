import CIL.Safety.LocalSnapshotSteps
import CIL.Safety.SymbolicExecution
import UInt256.Methods.Subtract.Vector256Bodies
import UInt256.Methods.Subtract.Vector256Math
import UInt256.Safety.VectorFrame
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.StepComposition
import UInt256.Methods.AddSubtract.BroadcastLookup

/-!
Checked AVX2 subtraction paths compose shared instruction rules with the live vector frame.
-/

namespace UInt256Proof.Subtract.Vector256
open CIL.Safety UInt256Model.Safety
variable {identity : Nat} {assembly : String}

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

/-- Argument formation and profile facts every instruction of the AVX2 bodies may read. -/
theorem impl_facts {program : CIL.Program} {original entered current : Memory}
    {left right output : Reference} {frame : Frame} {known : Nat → Option CIL.Value}
    {stored : Option (BitVec 256)} {profile : CIL.FeatureProfile} {avx512 bmi1 : Bool}
    (features : ImplProfile profile avx512 bmi1)
    (state : VectorFrame program original entered current [left, right] output frame known stored) :
    form current left = .ok left ∧ form current right = .ok right ∧
      form current output = .ok output ∧ profile.avx = true ∧ profile.avx2 = true ∧
      profile.avx512F = avx512 ∧ profile.avx512FVL = avx512 ∧ profile.bmi1 = bmi1 :=
  ⟨state.call.input_formed (by simp), state.call.input_formed (by simp),
    state.call.output_formed (by simp), features.avx, features.avx2, features.wideF, features.wide,
    features.bits⟩

theorem impl_inputs (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
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
  have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call
    (by simp : left ∈ [left, right])
  have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input current left
  rw [state.input_value originalCall (by simp : left ∈ [left, right])] at castLeft
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, loadLeft, castLeft]
  refine state.run_store post originalCall homes found fun current state => ?_
  have loadRight := UInt256Proof.Equality.VectorPrimitive.load_input state.call
    (by simp : right ∈ [left, right])
  have castRight := UInt256Proof.Equality.VectorPrimitive.cast_input current right
  rw [state.input_value originalCall (by simp : right ∈ [left, right])] at castRight
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, loadRight, castRight]
  refine state.run_store post originalCall homes found fun current state => ?_
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate]
  refine state.run_store post originalCall homes found fun current state => ?_
  exact continuation current state

/-- Locals 0-4 after the borrow mask and its incoming shift. -/
def maskLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (differenceLocals left right) 3 (.v256 (borrowLanes left right))) 4
    (.v256 (borrowIncoming (borrowLanes left right)))

theorem impl_masks (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
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
  · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, differenceLocals]
    refine state.run_store post originalCall homes found fun current state => ?_
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, differenceLocals]
    rw [permute_incoming]
    refine state.run_store post originalCall homes found fun current state => ?_
    exact continuation current state
  · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, differenceLocals]
    rw [ternary_borrow_lanes]
    refine state.run_store post originalCall homes found fun current state => ?_
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, differenceLocals]
    rw [show ∀ mask, CIL.Vector.alignRight64 mask 0 3 = borrowIncoming mask from align_incoming]
    refine state.run_store post originalCall homes found fun current state => ?_
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate] until continuation current state

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
    (homes : CompleteWritableHomes entered original.nextIdentity
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
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, maskLocals, differenceLocals]
  refine state.run_output post originalCall homes found fun current state => ?_
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, maskLocals, differenceLocals]
  refine state.run_store post originalCall homes found fun current state => ?_
  replace state : VectorFrame program original entered current [left, right] output frame
    (equalLocals a b) (some (speculative a b)) := state
  by_cases decided : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0
  · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, equalLocals, maskLocals,
      differenceLocals, beq_iff_eq.mpr decided] until fast decided current state
  · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, equalLocals, maskLocals,
      differenceLocals, beq_eq_false_iff_ne.mpr decided] until slow decided current state
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
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, equalLocals, maskLocals,
    differenceLocals, CIL.NarrowKind.extend_ite_ofNat_one_zero]
  exact continuation
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
    (homes : CompleteWritableHomes entered original.nextIdentity
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
  iterate 5
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, equalLocals, maskLocals,
      differenceLocals]
    refine state.run_store post originalCall homes found fun current state => ?_
  exact continuation current state
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
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile avx512 bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
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
  obtain ⟨added, row⟩ := UInt256Proof.AddSubtract.Vector256.table_row current reference
    state.call.1.1 loaded (UInt256Proof.SIMD.cascadeIndex
      (CIL.Vector.moveMask64 (borrowLanes a b)) (CIL.Vector.moveMask64 (equalLanes a b)))
    (UInt256Proof.SIMD.cascade_index_bound _ _)
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, equalLocals, maskLocals,
    differenceLocals, formed, added, row, CIL.offsetValue]
  refine state.run_store post originalCall homes found fun current state => ?_
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, equalLocals, maskLocals,
    differenceLocals]
  refine state.run_output post originalCall homes found fun stored state => ?_
  replace state : VectorFrame program original entered stored [left, right] output frame _
    (some (corrected a b)) := state
  cases bmi1
  · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, equalLocals,
      maskLocals, differenceLocals, CIL.NarrowKind.extend_ite_ofNat_one_zero]
    exact continuation stored state
  · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, equalLocals,
      maskLocals, differenceLocals]
    apply run_next_exists post found (op := .memory .bitcastByteBool) (by rfl)
    · cil_stack_cleanup
      rw [step_memory_bitcastByteBool_i32_eq, if_pos (bextr_bit _)]
    cil_contract_steps [found]
    rw [show ∀ flag : BitVec 8, CIL.NarrowKind.unsigned8.extend (flag.setWidth 32) =
      flag.setWidth 32 from fun flag => by simp [CIL.NarrowKind.extend]]
    exact continuation stored state

end UInt256Proof.Subtract.Vector256
