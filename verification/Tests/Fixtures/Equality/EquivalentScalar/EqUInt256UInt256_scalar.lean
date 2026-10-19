import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.PrimitiveOperator
import UInt256.Methods.ValueForwarder32
import CIL.SymbolicExecution
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import UInt256.Methods.Equality.Lemmas
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition


namespace EqualityFixture.Leaf

open CIL.Safety UInt256Model.Safety

/-- Short-circuit limb comparison: three early exits, then the high-limb equality. -/
def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .fieldAt 0 8,
  .bne 21,
  .arg 0,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 8 8,
  .bne 21,
  .arg 0,
  .fieldAt 16 8,
  .arg 1,
  .fieldAt 16 8,
  .bne 21,
  .arg 0,
  .fieldAt 24 8,
  .arg 1,
  .fieldAt 24 8,
  .eq,
  .ret (some .unsigned8),
  .const32 0,
  .ret (some .unsigned8)] }

def limbsEqual (memory : Memory) (left right : Reference) : BitVec 32 :=
  if inputLimb memory left 0 = inputLimb memory right 0 then
    if inputLimb memory left 1 = inputLimb memory right 1 then
      if inputLimb memory left 2 = inputLimb memory right 2 then
        if inputLimb memory left 3 = inputLimb memory right 3 then 1 else 0
      else 0
    else 0
  else 0

macro "leaf_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · assumption
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

variable (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
  (found : program[index]? = some (body profile))

include found in
theorem scalar_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (limbsEqual memory left right))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hc (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := rfl
  have hl0 := hl (0 : Fin 4)
  have hl1 := hl (1 : Fin 4)
  have hl2 := hl (2 : Fin 4)
  have hl3 := hl (3 : Fin 4)
  have hr0 := hr (0 : Fin 4)
  have hr1 := hr (1 : Fin 4)
  have hr2 := hr (2 : Fin 4)
  have hr3 := hr (3 : Fin 4)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at hl0 hl1 hl2 hl3 hr0 hr1 hr2 hr3
  refine ⟨28, ?_⟩
  by_cases e0 : inputLimb memory left 0 = inputLimb memory right 0
  · by_cases e1 : inputLimb memory left 1 = inputLimb memory right 1
    · by_cases e2 : inputLimb memory left 2 = inputLimb memory right 2
      · rw [show limbsEqual memory left right = if inputLimb memory left 3 = inputLimb memory right 3 then 1 else 0 by
          simp [limbsEqual, e0, e1, e2]]
        leaf_steps 20 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0, e1, e2
        simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        split <;> rfl
      · rw [show limbsEqual memory left right = 0 by simp [limbsEqual, e0, e1, e2]]
        leaf_steps 16 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0, e1, e2
        simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rw [show limbsEqual memory left right = 0 by simp [limbsEqual, e0, e1]]
      leaf_steps 11 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0, e1
      simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rw [show limbsEqual memory left right = 0 by simp [limbsEqual, e0]]
    leaf_steps 6 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, e0
    simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms scalar_run

theorem limbs_equal_value (memory : Memory) (left right : Reference) :
    limbsEqual memory left right = if inputValue memory left = inputValue memory right then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  clear leftValue rightValue
  simp only [UInt256Proof.Equality.value_eq_iff, limbsEqual]
  by_cases e0 : inputLimb memory left 0 = inputLimb memory right 0 <;>
    by_cases e1 : inputLimb memory left 1 = inputLimb memory right 1 <;>
    by_cases e2 : inputLimb memory left 2 = inputLimb memory right 2 <;>
    simp [e0, e1, e2]

include found in
theorem scalar_run_value (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  simpa only [limbs_equal_value] using scalar_run profile program index found memory left right frame call

theorem scalar_frame_fits (left right : Reference) :
    FrameSetupFits (body profile) (readOnlyArguments [left, right]) := by
  simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit]

include found in
theorem scalar_checked (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile)
    (fun left right => .i32 (if left = right then 1 else 0))
    found (scalar_frame_fits profile) (scalar_run_value profile program index found) memory left right call

#print axioms limbs_equal_value
#print axioms scalar_checked

end EqualityFixture.Leaf


namespace EqualityFixture.LeafReference
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 12,
  .feature .sse41,
  .brnonzero 8,
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }
theorem executed (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = false) (sse : profile.sse41 = false)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (EqualityFixture.Leaf.body profile))
    (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  let childFrame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  obtain ⟨childFuel, childRun⟩ := EqualityFixture.Leaf.scalar_run_value profile program callee leafFound memory left right childFrame call
  have child : invoke program childFuel callee (readOnlyArguments [left, right]) memory =
      .ok (memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
    apply invoke_of_run leafFound
    · simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rfl
    · simpa [leaveFrame, childFrame] using childRun
  have returnTrace : run program 1 index 7 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
    split <;> simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (body profile callee) (.call callee 2) 6 (readOnlyArguments [left, right]) frame
      [.reference (.address right), .reference (.address left)] memory =
      .ok (.call callee (readOnlyArguments [left, right]) [] memory) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, child⟩ ⟨1, returnTrace⟩
  refine ⟨fuel + 6, ?_⟩
  iterate 6
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false }) [body, step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
          pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate, vector, sse,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl, rfl, rfl, rfl⟩
  exact tail

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = false) (sse : profile.sse41 = false)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (EqualityFixture.Leaf.body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile callee)
    (fun left right => .i32 (if left = right then 1 else 0)) found
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit])
    (executed profile program index callee vector sse found leafFound) memory left right call

#print axioms executed
#print axioms checked
end EqualityFixture.LeafReference

/-- EquivalentScalar fixture for EqUInt256UInt256 on scalar, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ReadOnlyContract (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0)) Extracted.program Extracted.entryIndex 2 :=
  by
  change UInt256Model.Safety.ReadOnlyContract _ Extracted.program 0 2
  apply (by simpa using UInt256Proof.Equality.ReferenceOperator.readOnly_contract (fun a b => decide (a = b)) Extracted.program 0)
  intro memory left right call
  simpa using ((UInt256Proof.Equality.ReferenceOperator.checked (fun a b => decide (a = b)) Extracted.profile false Extracted.program 0 1 rfl
    (fun m l r c => by simpa using ((EqualityFixture.LeafReference.checked Extracted.profile Extracted.program 1 2 rfl rfl rfl rfl)) m l r c))) memory left right call

#print axioms EqualityFixture.correct
