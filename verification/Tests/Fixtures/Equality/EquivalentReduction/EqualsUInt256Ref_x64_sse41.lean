import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.PrimitiveOperator
import UInt256.Methods.ValueForwarder32
import UInt256.Methods.Equality.HalfSafetyFacts
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition

namespace EqualityFixture.LeafSse
open UInt256Proof UInt256Proof.Equality UInt256Proof.Equality.Safety
open CIL.Safety UInt256Model.Safety
 theorem intrinsic_equal128 (a b : BitVec 128) : CIL.evalIntrinsic (.vector (.equalsAll 128)) [.v128 a,.v128 b] = some (.i32 (if a = b then 1 else 0)) := by
  change some (CIL.Value.i32 (if a == b then 1 else 0)) = _
  simp
 theorem intrinsic_xor128 (a b : BitVec 128) : CIL.evalIntrinsic (.vector (.bxor 128)) [.v128 a,.v128 b] = some (.v128 (a ^^^ b)) := rfl
 theorem intrinsic_or128 (a b : BitVec 128) : CIL.evalIntrinsic (.vector (.bor 128)) [.v128 a,.v128 b] = some (.v128 (a ||| b)) := rfl
 theorem intrinsic_zero128 : CIL.evalIntrinsic (.vector (.zero 128)) [] = some (.v128 0) := rfl
def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [.nullRef, .nullRef], localKinds := [.reference, .reference], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .memory .asRef,
  .memory .asRef,
  .setLocal 0,
  .arg 1,
  .memory .asRef,
  .memory .asRef,
  .setLocal 1,
  .local 0,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .local 1,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .intrinsic (.vector (.bxor 128)) 2,
  .local 0,
  .memory .load128,
  .local 1,
  .memory .load128,
  .intrinsic (.vector (.bxor 128)) 2,
  .intrinsic (.vector (.bor 128)) 2,
  .intrinsic (.vector (.zero 128)) 0,
  .intrinsic (.vector (.equalsAll 128)) 2,
  .ret (some .unsigned8)] }
/-- Execute the extracted SSE leaf with its two managed-reference locals. -/
theorem sse_run (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat) (found : program[index]? = some (body profile)) (memory : Memory) (left right : Reference) (frame : Frame)
    (first second : Option ManagedReference)
    (locals : frame.locals = [.root first, .root second])
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := call.input_half_load (reference := left) (by simp)
  have hr := call.input_half_load (reference := right) (by simp)
  have al := call.input_half_address (reference := left) (by simp)
  have ar := call.input_half_address (reference := right) (by simp)
  have hl0 := hl 0
  have hr0 := hr 0
  have al1 := al 1
  have ar1 := ar 1
  have hl1 := hl 1
  have hr1 := hr 1
  simp only [Fin.val_one, Nat.mul_one] at al1 ar1 hl1 hr1
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hl0 hr0
  have difference := input_half_difference_zero memory left right
  rw [BitVec.or_comm] at difference

  clear hl hr al ar
  generalize loLeft : inputHalf memory left 0 = ll at *
  generalize hiLeft : inputHalf memory left 1 = lh at *
  generalize loRight : inputHalf memory right 0 = rl at *
  generalize hiRight : inputHalf memory right 1 = rh at *
  generalize valueLeft : inputValue memory left = vl at *
  generalize valueRight : inputValue memory right = vr at *
  refine ⟨26, ?_⟩
  iterate 25
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [body, step, checkedIntrinsic, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl0, hr0, hl1, hr1, al1, ar1,
            locals, storeLocal, loadLocal, pureArity, scalars, staticInstruction, memoryInstruction,
            CIL.step.eq_def, CIL.Intrinsic.available, intrinsic_equal128, intrinsic_xor128, intrinsic_or128, intrinsic_zero128,
            difference, instruction, CIL.offsetValue, referenceAt,
             checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  split <;> simp [run, found, body, step, checkedValue, numericValue, leaveFrame, CIL.NarrowKind.extend, * ,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]


#print axioms sse_run
end EqualityFixture.LeafSse





namespace EqualityFixture.LeafSse
open UInt256Proof UInt256Proof.Equality UInt256Proof.Equality.Safety
open CIL.Safety UInt256Model.Safety
theorem sse_frame_fits (profile : CIL.FeatureProfile) (left right : Reference) :
    FrameSetupFits (body profile) (readOnlyArguments [left, right]) := by

  simp [body, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit]

theorem sse_frame_roots (profile : CIL.FeatureProfile) (memory : Memory) (left right : Reference)
    (frame : Frame) (entered : Memory)
    (setup : enterFrame (body profile) (readOnlyArguments [left, right]) memory = .ok (frame, entered)) :
    frame.locals = [.root (some .null), .root (some .null)] := by

  simp [body, enterFrame, makeLocals, makeLocal, makeArgumentHomes, makeParameterHomes,
    Bind.bind, Except.bind, Pure.pure, Except.pure] at setup
  obtain ⟨rfl, rfl⟩ := setup
  rfl

theorem sse_checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat) (found : program[index]? = some (body profile)) (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary_frame program index (body profile)
    (fun left right => .i32 (if left = right then 1 else 0))
    found (sse_frame_fits profile)
    (fun frame => frame.locals = [.root (some .null), .root (some .null)])
    (sse_frame_roots profile)
    (fun memory left right frame roots call =>
      sse_run profile program index found memory left right frame (some .null) (some .null) roots call)
    memory left right call

#print axioms sse_frame_roots
#print axioms sse_checked

end EqualityFixture.LeafSse

namespace EqualityFixture.LeafSseWrapper
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 12,
  .feature .sse41,
  .brnonzero 8,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }
theorem executed (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = false) (sse : profile.sse41 = true)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (EqualityFixture.LeafSse.body profile))
    (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  let childFrame : Frame := ⟨memory.nextIdentity, [.root (some .null), .root (some .null)], [], []⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  obtain ⟨childFuel, childRun⟩ := EqualityFixture.LeafSse.sse_run profile program callee leafFound memory left right childFrame (some .null) (some .null) rfl call
  have child : invoke program childFuel callee (readOnlyArguments [left, right]) memory =
      .ok (memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
    apply invoke_of_run leafFound
    · simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rfl
    · simpa [leaveFrame, childFrame] using childRun
  have returnTrace : run program 1 index 11 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
    split <;> simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (body profile callee) (.call callee 2) 10 (readOnlyArguments [left, right]) frame
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
    (vector : profile.vector256Accelerated = false) (sse : profile.sse41 = true)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (EqualityFixture.LeafSse.body profile))
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
end EqualityFixture.LeafSseWrapper

/-- EquivalentReduction fixture for EqualsUInt256Ref on x64-sse41, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ReadOnlyContract (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0)) Extracted.program 0 2 :=
  by
  change UInt256Model.Safety.ReadOnlyContract _ Extracted.program 0 2
  apply (by simpa using UInt256Proof.Equality.ReferenceOperator.readOnly_contract (fun a b => decide (a = b)) Extracted.program 0)
  intro memory left right call
  simpa using ((EqualityFixture.LeafSseWrapper.checked Extracted.profile Extracted.program 0 1 rfl rfl rfl rfl)) memory left right call

#print axioms EqualityFixture.correct
