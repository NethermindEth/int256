import CIL.Safety.LocalSnapshotSteps
import CIL.Safety.SymbolicExecution
import CIL.Safety.NumericHomes
import UInt256.Methods.Subtract.Vector256Bodies
import UInt256.Methods.Subtract.Vector256Math
import UInt256.Methods.Add.VectorArithmeticDefinitions
import UInt256.Safety.VectorFrame
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.StepComposition
import UInt256.Methods.AddSubtract.BroadcastLookup

/-!
Checked AVX2 subtraction paths compose shared instruction rules with the live vector frame.
Each path is stepped once for the extracted body and for the blended one.
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

/-- The nine zero-initialised locals of either SubtractImpl body. -/
def implSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩,
   ⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩,
   ⟨.word32, .i32 0, 0, rfl⟩, ⟨.word32, .i32 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩]

/-- `body` is the extracted `SubtractImpl` or the blended one. The blended borrow masks are five
    instructions shorter, so the code after them starts `shift` past the blended position. -/
def ImplVariant (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool) (lookup : Nat)
    (body : CIL.Method) (shift : Nat) : Prop :=
  body = subtractImplBody profile avx512 bmi1 lookup ∧ shift = 5 ∨
    avx512 = false ∧ body = Blended.subtractBlendImplBody profile bmi1 lookup ∧ shift = 0

/-- Either body runs under the profile it was extracted for. -/
theorem ImplVariant.profile_eq {profile : CIL.FeatureProfile} {avx512 bmi1 : Bool} {lookup : Nat}
    {body : CIL.Method} {shift : Nat}
    (variant : ImplVariant profile avx512 bmi1 lookup body shift) : body.profile = profile := by
  rcases variant with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl

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

/-- A permute blended with zero in its low lane is the incoming borrow of each lane. -/
theorem blend_incoming (mask : BitVec 256) :
    CIL.Vector.blend32 (CIL.Vector.permute4x64 mask 144#8) 0 3#8 = borrowIncoming mask := by
  rw [← CIL.Vector.pack256_lanes mask]
  exact (UInt256Proof.Add.Safety.incomingCarry_packed _ _ _ _).trans (incoming_packed _ _ _ _).symm

/-- Locals 0-4: both operands, the lane differences, the borrow mask and its incoming shift. -/
def maskLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (rememberLocal (rememberLocal (rememberLocal (fun _ => none)
    0 (.v256 left)) 1 (.v256 right)) 2 (.v256 (CIL.Vector.zip256 (· - ·) left right)))
    3 (.v256 (borrowLanes left right))) 4 (.v256 (borrowIncoming (borrowLanes left right)))

/-- Both operands are loaded and the borrow masks formed, by either mask form or the blend. -/
theorem impl_masks (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (body : CIL.Method) (shift : Nat)
    (variant : ImplVariant profile avx512 bmi1 lookup body shift)
    (found : program[method]? = some body) (features : ImplProfile profile avx512 bmi1)
    (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (setup : enterFrame body (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : CompleteWritableHomes entered memory.nextIdentity
      (implSpecs.map NumericLocalSpec.kind) frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program memory entered after [left, right] output frame
        (maskLocals (inputValue memory left) (inputValue memory right)) none →
      ∃ fuel final values,
        run program fuel method (45 + shift) (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (final, values) ∧ post final values := by
  have profileEq := variant.profile_eq
  have state := VectorFrame.initial call setup
  have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call
    (by simp : left ∈ [left, right])
  have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input entered left
  rw [state.input_value call (by simp : left ∈ [left, right])] at castLeft
  obtain ⟨enteredFormed, formed, authority, valid, preserved⟩ :=
    state.walk_facts memory.nextIdentity
  rcases variant with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  case' inl => cases avx512
  all_goals
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, loadLeft, castLeft]
    replace state := state.after_stores call localSnapshots
    have loadRight := UInt256Proof.Equality.VectorPrimitive.load_input state.call
      (by simp : right ∈ [left, right])
    have castRight := UInt256Proof.Equality.VectorPrimitive.cast_input storedLocal right
    rw [state.input_value call (by simp : right ∈ [left, right])] at castRight
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, loadRight, castRight]
    simp only [ternary_borrow_lanes, permute_incoming, blend_incoming, ← borrowLanes.eq_1,
      show ∀ mask, CIL.Vector.alignRight64 mask 0 3 = borrowIncoming mask from align_incoming]
      at localSnapshots_4
    exact continuation _ (state.after_stores call localSnapshots_4)

/-- The first output store writes the speculative difference. -/
def speculative (left right : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (· + ·) (CIL.Vector.zip256 (· - ·) left right) (borrowIncoming (borrowLanes left right))

/-- Locals after the equal lanes, the cascade sum and the table index of the two lane masks. -/
def slowLocals (left right : BitVec 256) : Nat → Option CIL.Value :=
  let g := CIL.Vector.moveMask64 (borrowLanes left right)
  let p := CIL.Vector.moveMask64 (equalLanes left right)
  rememberLocal (rememberLocal (rememberLocal (rememberLocal (rememberLocal (rememberLocal
    (maskLocals left right) 5 (.v256 (equalLanes left right))) 6 (.i32 g)) 7 (.i32 p))
    6 (.i32 (p + 2 * g))) 7 (.i32 (p ^^^ (p + 2 * g)))) 7
    (.i32 (UInt256Proof.SIMD.cascadeIndex g p))

/-- The speculative store and the borrow decision: the fast path returns the top borrow, the
    slow path reaches the table lookup with the cascade index. -/
theorem impl_decision (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (body : CIL.Method) (shift : Nat)
    (variant : ImplVariant profile avx512 bmi1 lookup body shift)
    (found : program[method]? = some body) (features : ImplProfile profile avx512 bmi1)
    (memory entered current : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (homes : CompleteWritableHomes entered memory.nextIdentity
      (implSpecs.map NumericLocalSpec.kind) frame.locals)
    (a b : BitVec 256)
    (state : VectorFrame program memory entered current [left, right] output frame
      (maskLocals a b) none)
    (post : Memory → List Value → Prop)
    (fast : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0 → ∀ after known,
      VectorFrame program memory entered after [left, right] output frame known
        (some (speculative a b)) →
      post (leaveFrame frame after) [.scalar (.i32
        (if 0#32 < CIL.Vector.moveMask64 (borrowLanes a b) &&& 8#32 then 1#32 else 0#32))])
    (slow : ∀ after,
      VectorFrame program memory entered after [left, right] output frame (slowLocals a b)
        (some (speculative a b)) →
      ∃ fuel final values,
        run program fuel method (83 + shift) (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method (45 + shift) (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq := variant.profile_eq
  rcases variant with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, maskLocals]
    refine state.run_output post call homes found fun current state => ?_
    obtain ⟨enteredFormed, formed, authority, valid, preserved⟩ :=
      state.walk_facts memory.nextIdentity
    by_cases decided : CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) a b &&&
        borrowIncoming (borrowLanes a b) = 0
    · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
        impl_facts features state, CIL.FeatureProfile.evaluate, maskLocals, decided,
        CIL.NarrowKind.extend_ite_ofNat_one_zero]
      exact fast decided _ _ (state.after_stores call localSnapshots)
    · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
        impl_facts features state, CIL.FeatureProfile.evaluate, maskLocals, decided]
      exact slow _ (state.after_stores call localSnapshots_5)

/-- The corrected difference after the table lookup. -/
def corrected (left right : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (· - ·) (CIL.Vector.zip256 (· - ·) left right)
    (UInt256Proof.SIMD.cascadeVector (UInt256Proof.SIMD.cascadeIndex
      (CIL.Vector.moveMask64 (borrowLanes left right)) (CIL.Vector.moveMask64 (equalLanes left right))))

/-- The BMI1 extraction of bit 4 is a byte holding zero or one. -/
theorem bextr_bit (x : BitVec 32) :
    (((CIL.Vector.bextr32 x 4 1).setWidth 8).setWidth 32).toNat ≤ 1 := by
  simp [CIL.Vector.bextr32]
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))

/-- The table lookup, the corrected store and the borrow out of the cascade sum. -/
theorem impl_slow_tail (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (body : CIL.Method) (shift : Nat)
    (variant : ImplVariant profile avx512 bmi1 lookup body shift)
    (found : program[method]? = some body)
    (lookupFound : program[lookup]? =
      some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile avx512 bmi1)
    (memory entered current : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (homes : CompleteWritableHomes entered memory.nextIdentity
      (implSpecs.map NumericLocalSpec.kind) frame.locals)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program memory entered current [left, right] output frame
      (slowLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after known,
      VectorFrame program memory entered after [left, right] output frame known
        (some (corrected a b)) →
      post (leaveFrame frame after) [.scalar (.i32 (slowFlag bmi1
        (CIL.Vector.moveMask64 (equalLanes a b) + 2 * CIL.Vector.moveMask64 (borrowLanes a b))))]) :
    ∃ fuel final values,
      run program fuel method (83 + shift) (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq := variant.profile_eq
  rcases variant with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    apply UInt256Proof.AddSubtract.Vector256.run_lookup post state found (by rfl) lookupFound
    intro current reference state loaded formed
    obtain ⟨added, row⟩ := UInt256Proof.AddSubtract.Vector256.table_row current reference
      state.call.1.1 loaded (UInt256Proof.SIMD.cascadeIndex
        (CIL.Vector.moveMask64 (borrowLanes a b)) (CIL.Vector.moveMask64 (equalLanes a b)))
      (UInt256Proof.SIMD.cascade_index_bound _ _)
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, maskLocals, formed,
      added, row, CIL.offsetValue]
    refine state.run_store post call homes found fun current state => ?_
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, maskLocals]
    refine state.run_output post call homes found fun stored state => ?_
    cases bmi1
    · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
        impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, maskLocals,
        CIL.NarrowKind.extend_ite_ofNat_one_zero]
      exact continuation stored _ state
    · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
        impl_facts features state, CIL.FeatureProfile.evaluate, slowLocals, maskLocals]
      apply run_next_exists post found (op := .memory .bitcastByteBool) (by rfl)
      · cil_stack_cleanup
        rw [step_memory_bitcastByteBool_i32_eq, if_pos (bextr_bit _)]
      cil_contract_steps [found]
      rw [show ∀ flag : BitVec 8, CIL.NarrowKind.unsigned8.extend (flag.setWidth 32) =
        flag.setWidth 32 from fun flag => by simp [CIL.NarrowKind.extend]]
      exact continuation stored _ state

end UInt256Proof.Subtract.Vector256
