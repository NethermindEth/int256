import CIL.Safety.Equations
import UInt256.Methods.Subtract.Vector256Contract
import UInt256.Methods.Add.VectorArithmeticDefinitions
import UInt256.Safety.ReportingForwarder

namespace UInt256Proof.Subtract.Vector256.Blended
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Vector256
variable {identity : Nat} {assembly : String}

/-- AVX2 `SubtractImpl` that forms the incoming borrows with a permute and a zero blend. -/
def subtractBlendImplBody (profile : CIL.FeatureProfile) (bmi1 : Bool) (lookup : Nat) :
    CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize (← `(
    let template := subtractImplBody $(Lean.mkIdent `profile) false
      $(Lean.mkIdent `bmi1) $(Lean.mkIdent `lookup)
    let incoming : List CIL.Op := [.intrinsic (.vector (.reinterpret 256)) 1,
      .intrinsic (.vector (.zero 256)) 0, .const32 3,
      .intrinsic (.avx2 .blend32) 3, .intrinsic (.vector (.reinterpret 256)) 1]
    { template with code := ((template.code.take 39 ++ incoming ++ template.code.drop 49)
        |>.set 1 (.brzero 120) |>.set 60 (.brnonzero 112) |>.set 98 (.brnonzero 105)) })) none
  let names := #[``subtractImplBody, ``List.take, ``List.drop, ``List.set,
    ``List.append, ``HAppend.hAppend, ``Append.append]
  let rules ← names.foldlM (fun rules name => rules.addDeclToUnfold name)
    ({} : Lean.Meta.SimpTheorems)
  let context ← Lean.Meta.Simp.mkContext (simpTheorems := #[rules])
  let normalized := (← Lean.Meta.dsimp body context).1
  let rules ← #[``eq_self, ``ite_true, ``ite_false].foldlM
    (fun rules name => rules.addConst name) ({} : Lean.Meta.SimpTheorems)
  let context ← Lean.Meta.Simp.mkContext (simpTheorems := #[rules])
  return (← Lean.Meta.simp normalized context).1.expr
theorem blend_incoming (mask : BitVec 256) :
    CIL.Vector.blend32 (CIL.Vector.permute4x64 mask (BitVec.ofNat 8 144)) (BitVec.ofNat 256 0) (BitVec.ofNat 8 3) =
      borrowIncoming mask := by
  rw [← CIL.Vector.pack256_lanes mask]
  exact (UInt256Proof.Add.Safety.incomingCarry_packed _ _ _ _).trans (incoming_packed _ _ _ _).symm

theorem impl_inputs (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (bmi1 : Bool) (found : program[method]? = some (subtractBlendImplBody profile bmi1 lookup))
    (features : ImplProfile profile false bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
      (subtractBlendImplBody profile bmi1 lookup).localKinds frame.locals)
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
  have profileEq : (subtractBlendImplBody profile bmi1 lookup).profile = profile := rfl
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
theorem impl_masks (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (bmi1 : Bool) (found : program[method]? = some (subtractBlendImplBody profile bmi1 lookup))
    (features : ImplProfile profile false bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
      (subtractBlendImplBody profile bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (differenceLocals a b) none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame (maskLocals a b) none →
      ∃ fuel final values,
        run program fuel method 45 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 14 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractBlendImplBody profile bmi1 lookup).profile = profile := rfl
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, differenceLocals]
  refine state.run_store post originalCall homes found fun current state => ?_
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, differenceLocals]
  rw [show ∀ mask, CIL.Vector.blend32 (CIL.Vector.permute4x64 mask 144#8) 0 3#8 =
    borrowIncoming mask from blend_incoming]
  refine state.run_store post originalCall homes found fun current state => ?_
  exact continuation current state
theorem impl_decision (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (bmi1 : Bool) (found : program[method]? = some (subtractBlendImplBody profile bmi1 lookup))
    (features : ImplProfile profile false bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
      (subtractBlendImplBody profile bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (maskLocals a b) none)
    (post : Memory → List Value → Prop)
    (fast : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0 → ∀ after,
      VectorFrame program original entered after [left, right] output frame (equalLocals a b)
        (some (speculative a b)) →
      ∃ fuel final values,
        run program fuel method 112 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values)
    (slow : equalLanes a b &&& borrowIncoming (borrowLanes a b) ≠ 0 → ∀ after,
      VectorFrame program original entered after [left, right] output frame (equalLocals a b)
        (some (speculative a b)) →
      ∃ fuel final values,
        run program fuel method 61 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 45 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractBlendImplBody profile bmi1 lookup).profile = profile := rfl
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
      differenceLocals, decided] until fast decided current state
  · cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, equalLocals, maskLocals,
      differenceLocals, decided] until slow decided current state
theorem impl_fast_return (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (bmi1 : Bool) (found : program[method]? = some (subtractBlendImplBody profile bmi1 lookup))
    (features : ImplProfile profile false bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (equalLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : post (leaveFrame frame current)
      [.scalar (.i32 (if 0#32 < CIL.Vector.moveMask64 (borrowLanes a b) &&& 8#32 then 1#32 else 0#32))]) :
    ∃ fuel final values,
      run program fuel method 112 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractBlendImplBody profile bmi1 lookup).profile = profile := rfl
  cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
    impl_facts features state, CIL.FeatureProfile.evaluate, equalLocals, maskLocals,
    differenceLocals, CIL.NarrowKind.extend_ite_ofNat_one_zero]
  exact continuation
theorem impl_index (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (bmi1 : Bool) (found : program[method]? = some (subtractBlendImplBody profile bmi1 lookup))
    (features : ImplProfile profile false bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
      (subtractBlendImplBody profile bmi1 lookup).localKinds frame.locals)
    (a b : BitVec 256) (value : BitVec 256)
    (state : VectorFrame program original entered current [left, right] output frame (equalLocals a b) (some value))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [left, right] output frame (slowLocals a b) (some value) →
      ∃ fuel final values,
        run program fuel method 83 (binaryArguments left right output) frame [] after =
          .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method 61 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractBlendImplBody profile bmi1 lookup).profile = profile := rfl
  iterate 5
    cil_contract_steps (snapshots := state.locals) [found, binaryArguments, profileEq,
      impl_facts features state, CIL.FeatureProfile.evaluate, equalLocals, maskLocals,
      differenceLocals]
    refine state.run_store post originalCall homes found fun current state => ?_
  exact continuation current state
theorem impl_slow_tail (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (bmi1 : Bool) (found : program[method]? = some (subtractBlendImplBody profile bmi1 lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile false bmi1)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity
      (subtractBlendImplBody profile bmi1 lookup).localKinds frame.locals)
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
      run program fuel method 83 (binaryArguments left right output) frame [] current =
        .ok (final, values) ∧ post final values := by
  have profileEq : (subtractBlendImplBody profile bmi1 lookup).profile = profile := rfl
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

/-- Blended AVX2 `SubtractImpl`: the exact initial-operand borrow, the wrapped difference, a writable output and
    unchanged caller bytes outside it, for either borrow-mask form and either flag extraction. -/
theorem impl_contract (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (bmi1 : Bool) (found : program[method]? = some (subtractBlendImplBody profile bmi1 lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile false bmi1) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program method := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds
    (body := subtractBlendImplBody profile bmi1 lookup)
    (by simp [subtractBlendImplBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit,
      ParameterArgumentsFit, SelectedKindsFit])
  obtain ⟨frame', entered', setup', homes, _, wf⟩ := numeric_frame_setup
    (subtractBlendImplBody profile bmi1 lookup) implSpecs rfl rfl rfl rfl rfl memory
    (binaryArguments left right output) call.1.1
  rw [setup] at setup'
  cases setup'
  have writable : CompleteWritableHomes entered memory.nextIdentity
      (subtractBlendImplBody profile bmi1 lookup).localKinds frame.locals :=
    CIL.Safety.NumericHomes.complete homes
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
    apply impl_inputs program method lookup profile bmi1 found features memory entered entered
      left right output frame call writable state post
    intro after state
    apply impl_masks program method lookup profile bmi1 found features memory entered after
      left right output frame call writable _ _ state post
    intro after state
    apply impl_decision program method lookup profile bmi1 found features memory entered after
      left right output frame call writable _ _ state post
    · intro fast after state
      apply impl_fast_return program method lookup profile bmi1 found features memory entered after
        left right output frame _ _ _ state post
      obtain ⟨value, access, footprint⟩ := state.finish call owned
      exact ⟨by rw [fast_flag_bits _ _ fast]; rfl, value.trans (speculative_value _ _ fast), access, footprint⟩
    · intro _ after state
      apply impl_index program method lookup profile bmi1 found features memory entered after
        left right output frame call writable _ _ _ state post
      intro after state
      apply impl_slow_tail program method lookup profile bmi1 found lookupFound features memory entered
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

/-- Blended AVX2 `Subtract`: wrapped difference of the initial operands; the borrow flag is discarded. -/
theorem subtract_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (bmi1 : Bool)
    (entryFound : program[0]? = some (subtractEntryBody profile 1))
    (implFound : program[1]? = some (subtractBlendImplBody profile bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile false bmi1) :
    WrappingBinaryContract (· - ·) program 0 :=
  forward_reporting_pop program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile bmi1 implFound lookupFound features)

/-- Blended AVX2 `SubtractUnderflow`: wrapped difference and the exact initial-operand borrow. -/
theorem subtract_underflow_contract (program : CIL.Program) (profile : CIL.FeatureProfile) (bmi1 : Bool)
    (entryFound : program[0]? = some (subtractUnderflowEntryBody profile 1))
    (implFound : program[1]? = some (subtractBlendImplBody profile bmi1 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (features : ImplProfile profile false bmi1) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program 0 :=
  forward_reporting_byte program 0 1 _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (impl_contract program 1 2 profile bmi1 implFound lookupFound features)

end UInt256Proof.Subtract.Vector256.Blended
