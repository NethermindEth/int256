import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.Equality.SseSafetyContract
import CIL.Safety.CallComposition
namespace UInt256Proof.Equality.ReferenceSseWrapper
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
    (leafFound : program[callee]? = some (Safety.body profile))
    (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  let childFrame : Frame := ⟨memory.nextIdentity, [.root (some .null), .root (some .null)], [], []⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  obtain ⟨childFuel, childRun⟩ := Safety.sse_run profile program callee leafFound memory left right childFrame (some .null) (some .null) rfl call
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
    split <;> simp [run, found, body, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (body profile callee) (.call callee 2) 10 (readOnlyArguments [left, right]) frame
      [.reference (.address right), .reference (.address left)] memory =
      .ok (.call callee (readOnlyArguments [left, right]) [] memory) := by
    simp [step, cil_guard, observerCount, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, child⟩ ⟨1, returnTrace⟩
  refine ⟨fuel + 6, ?_⟩
  have vectorOff : profile.evaluate .vector256Accelerated = false := vector
  have sseOn : profile.evaluate .sse41 = true := sse
  cil_checked_steps 6 [body, readOnlyArguments, fl, fr, vectorOff, sseOn]
  exact tail

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = false) (sse : profile.sse41 = true)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (Safety.body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile callee)
    (fun left right => .i32 (if left = right then 1 else 0)) found
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit])
    (executed profile program index callee vector sse found leafFound) memory left right call

#print axioms executed
#print axioms checked
end UInt256Proof.Equality.ReferenceSseWrapper
