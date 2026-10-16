import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.PrimitiveOperator
import UInt256.Methods.ValueForwarder32
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition
import UInt256.Methods.Equality.VectorPrimitive


namespace EqualityFixture.LeafVector
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety UInt256Proof.Equality.VectorPrimitive

def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .arg 1,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .intrinsic (.vector (.bxor 256)) 2,
  .intrinsic (.vector (.zero 256)) 0,
  .intrinsic (.vector (.equalsAll 256)) 2,
  .ret (some .unsigned8)] }

theorem executed (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := load_input call (input := left) (by simp)
  have hr := load_input call (input := right) (by simp)
  have cl := cast_input memory left
  have cr := cast_input memory right
  generalize leftEq : inputValue memory left = leftValue at *
  generalize rightEq : inputValue memory right = rightValue at *
  refine ⟨11, ?_⟩
  iterate 9
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [body, step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl, hr, cl, cr, staticInstruction, checkedIntrinsic, pureArity, scalars,
            CIL.step.eq_def, CIL.Intrinsic.available, eval_xor, eval_zero, eval_equal,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl, rfl, rfl, rfl⟩
        done
  simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  split <;> rfl

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile)
    (fun left right => .i32 (if left = right then 1 else 0)) found
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit])
    (executed profile program index found) memory left right call

#print axioms executed
#print axioms checked
end EqualityFixture.LeafVector


namespace EqualityFixture.LeafVectorWrapper
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 12,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8)] }

theorem executed (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (EqualityFixture.LeafVector.body profile))
    (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  let childFrame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  obtain ⟨childFuel, childRun⟩ := EqualityFixture.LeafVector.executed profile program callee leafFound memory left right childFrame call
  have child : invoke program childFuel callee (readOnlyArguments [left, right]) memory =
      .ok (memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
    apply invoke_of_run leafFound
    · simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rfl
    · simpa [leaveFrame, childFrame] using childRun
  have returnTrace : run program 1 index 15 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
    split <;> simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (body profile callee) (.call callee 2) 14 (readOnlyArguments [left, right]) frame
      [.reference (.address right), .reference (.address left)] memory =
      .ok (.call callee (readOnlyArguments [left, right]) [] memory) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, child⟩ ⟨1, returnTrace⟩
  refine ⟨fuel + 4, ?_⟩
  iterate 4
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false }) [body, step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
          pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate, vector,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl, rfl, rfl, rfl⟩
  exact tail

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (EqualityFixture.LeafVector.body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile callee)
    (fun left right => .i32 (if left = right then 1 else 0)) found
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit])
    (executed profile program index callee vector found leafFound) memory left right call

#print axioms executed
#print axioms checked
end EqualityFixture.LeafVectorWrapper

/-- EquivalentReduction fixture for EqualsUInt256Ref on x64-vector256, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ReadOnlyContract (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0)) Extracted.program 0 2 :=
  by
  change UInt256Model.Safety.ReadOnlyContract _ Extracted.program 0 2
  apply (by simpa using UInt256Proof.Equality.ReferenceOperator.readOnly_contract (fun a b => decide (a = b)) Extracted.program 0)
  intro memory left right call
  simpa using ((EqualityFixture.LeafVectorWrapper.checked Extracted.profile Extracted.program 0 1 rfl rfl rfl)) memory left right call

#print axioms EqualityFixture.correct
