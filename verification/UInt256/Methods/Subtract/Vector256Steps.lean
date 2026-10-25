import UInt256.Methods.Subtract.Vector256Bodies
import UInt256.Methods.Subtract.Vector256Math
import UInt256.Safety.VectorFrame
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.StepComposition
import UInt256.Methods.AddSubtract.BroadcastLookup

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

set_option hygiene false in
/-- One pure instruction of the impl body; expects `post found features profileEq state left right output`. -/
macro "impl_pure" : tactic => `(tactic|
  (have formedLeft := state.call.input_formed (reference := left) (by simp)
   have formedRight := state.call.input_formed (reference := right) (by simp)
   have formedOutput := state.call.output_formed (reference := output) (by simp)
   apply run_next_exists post found (by rfl)
   · simp (config := { implicitDefEqProofs := false })
       [step, cil_guard, observerCount, pureArity, binaryArguments, checkedValue, numericValue, formValue, formedLeft, formedRight,
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

private theorem step_reference_arg {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference}
    (found : args[index]? = some (.reference (.address reference)))
    (formed : form memory reference = .ok reference) :
    step body (.arg index) pc args frame stack memory =
      .ok (.next (pc + 1) (.reference (.address reference) :: stack) frame memory) := by
  simp only [step, cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, found, checkedValue, formValue, formed, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem formed_value {memory : Memory} {reference : Reference}
    (formed : form memory reference = .ok reference) :
    formValue memory (.address reference) = .ok (.reference (.address reference)) := by
  show (checkedAt (.address reference) 0 (form memory reference) >>= fun result =>
    pure (Value.reference (.address result)) : ExecutionResult Value) = _
  rw [formed]
  rfl

private theorem step_instruction {body : CIL.Method} {op : CIL.Op} {pc : Nat} {args stack values : List Value}
    {frame : Frame} {memory after : Memory}
    (fallback : step body op pc args frame stack memory =
      (instruction op stack memory >>= fun result =>
        pure (FrameAction.next (pc + 1) result.2 frame result.1) : ExecutionResult FrameAction))
    (executed : instruction op stack memory = .ok (after, values)) :
    step body op pc args frame stack memory = .ok (.next (pc + 1) values frame after) := by
  rw [fallback, executed]
  rfl

private theorem step_memory {body : CIL.Method} {operation : CIL.MemoryOp} {pc : Nat}
    {args stack values : List Value} {frame : Frame} {memory after : Memory}
    (executed : memoryInstruction operation stack memory = .ok (after, values))
    (direct : staticInstruction body pc operation stack memory = memoryInstruction operation stack memory) :
    step body (.memory operation) pc args frame stack memory = .ok (.next (pc + 1) values frame after) := by
  have known : unspecifiedOperands operation.argumentCount stack = false := by
    cases observed : unspecifiedOperands operation.argumentCount stack
    · rfl
    · unfold memoryInstruction at executed
      simp only [observed, ite_true] at executed
      cases executed
  simp only [cil_step, known, direct, executed, Bool.false_eq_true, ite_false, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

private theorem step_skip_init {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference}
    (formed : form memory reference = .ok reference) :
    step body .skipInit pc args frame (.reference (.address reference) :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := by
  refine step_instruction rfl ?_
  show (formValue memory (.address reference) >>= fun _ =>
    pure (memory, rest) : ExecutionResult (Memory × List Value)) = _
  rw [formed_value formed]
  rfl

private theorem step_as_ref {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference}
    (formed : form memory reference = .ok reference) :
    step body (.memory .asRef) pc args frame (.reference (.address reference) :: rest) memory =
      .ok (.next (pc + 1) (.reference (.address reference) :: rest) frame memory) := by
  refine step_memory ?_ rfl
  show (formValue memory (.address reference) >>= fun value =>
    pure (memory, value :: rest) : ExecutionResult (Memory × List Value)) = _
  rw [formed_value formed]
  rfl

private theorem step_add_offset {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference result : Reference} {offset : BitVec 64}
    (added : add memory reference 32 (BitVec.ofInt 64 (offset.toNat : Int)) = .ok result) :
    step body (.memory (.add 32 false)) pc args frame
      (.scalar (.i64 offset) :: .reference (.address reference) :: rest) memory =
      .ok (.next (pc + 1) (.reference (.address result) :: rest) frame memory) := by
  refine step_memory ?_ rfl
  show (checkedAt (.address reference) 0 (add memory reference 32 (BitVec.ofInt 64 (offset.toNat : Int))) >>=
    fun address => pure (memory, Value.reference (.address address) :: rest) :
      ExecutionResult (Memory × List Value)) = _
  rw [added]
  rfl

private theorem step_load256 {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference} {value : CIL.Value}
    (loaded : loadValue memory (.address reference) 32 = .ok value) :
    step body (.memory .load256) pc args frame (.reference (.address reference) :: rest) memory =
      .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  refine step_memory ?_ rfl
  show (loadValue memory (.address reference) 32 >>= fun value =>
    pure (memory, Value.scalar value :: rest) : ExecutionResult (Memory × List Value)) = _
  rw [loaded]
  rfl

private theorem step_byte_bool {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {bits : BitVec 32} (small : bits.toNat ≤ 1) :
    step body (.memory .bitcastByteBool) pc args frame (.scalar (.i32 bits) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 bits) :: rest) frame memory) := by
  refine step_memory ?_ rfl
  show (if bits.toNat ≤ 1 then pure (memory, Value.scalar (.i32 bits) :: rest)
    else .error (.unsupported "Noncanonical Boolean representation") :
      ExecutionResult (Memory × List Value)) = _
  rw [ite_eq_left_of_eq_true _ _ (eq_true small)]
  rfl

private theorem step_span_reference {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference} {length : Nat}
    (formed : form memory reference = .ok reference) :
    step body (.memory .spanReference) pc args frame (.span (.address reference) length :: rest) memory =
      .ok (.next (pc + 1) (.reference (.address reference) :: rest) frame memory) := by
  refine step_memory ?_ rfl
  show (formValue memory (.address reference) >>= fun value =>
    pure (memory, value :: rest) : ExecutionResult (Memory × List Value)) = _
  rw [formed_value formed]
  rfl

set_option hygiene false in
/-- Replace the profile by its fields so feature and intrinsic checks reduce by `rfl`. -/
local macro "impl_concrete" : tactic => `(tactic|
  (obtain ⟨featureAvx, featureAvx2, featureWideF, featureWide, featureBits⟩ := features
   obtain ⟨architecture, nativeWidth, littleEndian, advSimd, sse2, ssse3, sse42, avx, avx2, avx512F,
     avx512FVL, bmi1', sse41, avx512DQ, avx512DQVL, bmi2, armBase64, vector256Accelerated⟩ := profile
   dsimp only at featureAvx featureAvx2 featureWideF featureWide featureBits
   subst avx avx2 avx512F avx512FVL bmi1'))

set_option hygiene false in
/-- One pure instruction step closed by definitional unfolding. -/
local macro "impl_step" : tactic => `(tactic|
  (apply run_next_exists post found (by rfl)
   · first
     | rfl
     | exact step_reference_arg rfl (state.call.input_formed (reference := left) (by simp))
     | exact step_reference_arg rfl (state.call.input_formed (reference := right) (by simp))
     | exact step_reference_arg rfl (state.call.output_formed (reference := output) (by simp))
     | exact step_skip_init (state.call.output_formed (reference := output) (by simp))
     | exact step_as_ref (state.call.output_formed (reference := output) (by simp))))

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
  impl_concrete
  have loadLeft := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : left ∈ [left, right])
  have castLeft := UInt256Proof.Equality.VectorPrimitive.cast_input current left
  have sameLeft := state.input_value originalCall (by simp : left ∈ [left, right])
  rw [sameLeft] at castLeft
  impl_step
  impl_step
  impl_step
  apply run_next_exists post found (by rfl)
  · exact step_instruction rfl (loadLeft [])
  apply run_next_exists post found (by rfl)
  · exact step_memory (castLeft []) rfl
  impl_store
  have loadRight := UInt256Proof.Equality.VectorPrimitive.load_input state.call (by simp : right ∈ [left, right])
  have castRight := UInt256Proof.Equality.VectorPrimitive.cast_input current right
  have sameRight := state.input_value originalCall (by simp : right ∈ [left, right])
  rw [sameRight] at castRight
  impl_step
  apply run_next_exists post found (by rfl)
  · exact step_instruction rfl (loadRight [])
  apply run_next_exists post found (by rfl)
  · exact step_memory (castRight []) rfl
  impl_store
  impl_load
  impl_load
  impl_step
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
  impl_concrete
  cases avx512
  · impl_step
    impl_step
    impl_load
    impl_load
    impl_step
    impl_store
    impl_load
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    show ∃ fuel result returned, run program fuel method _ _ frame [.scalar (.v256 (CIL.Vector.permute4x64 (borrowLanes a b) (BitVec.ofNat 8 144) &&&
      CIL.Vector.pack256 (BitVec.ofNat 64 0) (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 18446744073709551615)))] current =
        .ok (result, returned) ∧ post result returned
    rw [permute_incoming]
    impl_store
    exact continuation current state
  · impl_step
    impl_step
    impl_load
    impl_load
    impl_load
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    impl_step
    show ∃ fuel result returned, run program fuel method _ _ frame [.scalar (.v256 (CIL.Vector.map256 (fun x => x.sshiftRight 63)
      (CIL.Vector.ternaryLogic a b (CIL.Vector.zip256 (· - ·) a b) (BitVec.ofNat 8 142))))] current =
        .ok (result, returned) ∧ post result returned
    rw [ternary_borrow_lanes]
    impl_store
    impl_load
    impl_step
    impl_step
    impl_step
    show ∃ fuel result returned, run program fuel method _ _ frame [.scalar (.v256 (CIL.Vector.alignRight64 (borrowLanes a b) (BitVec.ofNat 256 0) 3))] current =
        .ok (result, returned) ∧ post result returned
    rw [align_incoming]
    impl_store
    impl_step
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
  impl_concrete
  impl_step
  impl_step
  impl_step
  impl_step
  impl_load
  impl_load
  impl_step
  obtain ⟨stored, storeStep, state⟩ := state.output_store originalCall homes
    _ 57 (binaryArguments left right output) []
    (speculative a b)
  apply run_next_exists post found (by rfl) storeStep
  impl_load
  impl_load
  impl_step
  impl_store
  impl_load
  impl_load
  impl_step
  show ∃ fuel result returned, run program fuel method _ _ frame
      [.scalar (.i32 (if (equalLanes a b &&& borrowIncoming (borrowLanes a b) == 0) then 1 else 0))] current =
        .ok (result, returned) ∧ post result returned
  by_cases decided : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0
  · rw [beq_iff_eq.mpr decided]
    impl_step
    exact fast decided current state
  · rw [beq_eq_false_iff_ne.mpr decided]
    impl_step
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
  have stepped : step (subtractImplBody profile avx512 bmi1 lookup) (.ret (some .unsigned8)) pc args frame
      [.scalar (.i32 flag)] memory =
      .ok (.returned [.scalar (.i32 (CIL.NarrowKind.unsigned8.extend flag))] memory) := rfl
  rw [normalized] at stepped
  exact run_return found fetched stepped rfl

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
  impl_concrete
  impl_load
  impl_step
  impl_step
  impl_step
  impl_step
  impl_step
  impl_step
  exact ⟨1, _, _, impl_return program method lookup _ avx512 bmi1 found 124 rfl _ frame current _
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
  impl_concrete
  impl_load
  impl_step
  impl_step
  impl_store
  impl_load
  impl_step
  impl_step
  impl_store
  impl_load
  impl_step
  impl_load
  impl_step
  impl_step
  impl_store
  impl_load
  impl_load
  impl_step
  impl_store
  impl_load
  impl_step
  impl_step
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
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
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
  impl_concrete
  apply UInt256Proof.AddSubtract.Vector256.run_lookup post state found (by rfl) lookupFound
  intro current reference state loaded formed
  obtain ⟨added, row⟩ := UInt256Proof.AddSubtract.Vector256.table_row current reference state.call.1.1 loaded
    (UInt256Proof.SIMD.cascadeIndex (CIL.Vector.moveMask64 (borrowLanes a b)) (CIL.Vector.moveMask64 (equalLanes a b)))
    (UInt256Proof.SIMD.cascade_index_bound _ _)
  apply run_next_exists post found (by rfl) (step_span_reference formed)
  apply run_next_exists post found (by rfl) (step_as_ref formed)
  impl_load
  impl_step
  apply run_next_exists post found (by rfl) (step_add_offset added)
  apply run_next_exists post found (by rfl) (step_load256 row)
  impl_store
  impl_step
  impl_step
  impl_load
  impl_load
  impl_step
  obtain ⟨stored, storeStep, state⟩ := state.output_store originalCall homes
    _ 101 (binaryArguments left right output) []
    (corrected a b)
  apply run_next_exists post found (by rfl) storeStep
  cases bmi1
  · impl_step
    impl_step
    impl_load
    impl_step
    impl_step
    impl_step
    impl_step
    exact ⟨1, _, _, impl_return program method lookup _ _ false found 109 rfl _ frame stored _
      (by split <;> rfl), continuation stored state⟩
  · impl_step
    impl_step
    impl_load
    impl_step
    impl_step
    impl_step
    impl_step
    apply run_next_exists post found (by rfl) (step_byte_bool (bextr_bit
      (CIL.Vector.moveMask64 (equalLanes a b) + 2#32 * CIL.Vector.moveMask64 (borrowLanes a b))))
    exact ⟨1, _, _, impl_return program method lookup _ _ true found 116 rfl _ frame stored _
      (by simp [CIL.NarrowKind.extend]), continuation stored state⟩

end UInt256Proof.Subtract.Vector256
