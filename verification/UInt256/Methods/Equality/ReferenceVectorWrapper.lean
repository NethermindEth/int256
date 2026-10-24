import CIL.Safety.CallComposition
import UInt256.Methods.Equality.ReferenceVector
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Equality.ReferenceVectorWrapper
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
    (leafFound : program[callee]? = some (ReferenceVector.body profile))
    (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  let childFrame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  obtain ⟨childFuel, childRun⟩ := ReferenceVector.executed profile program callee leafFound memory left right childFrame call
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
    split <;> simp [run, found, body, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (body profile callee) (.call callee 2) 14 (readOnlyArguments [left, right]) frame
      [.reference (.address right), .reference (.address left)] memory =
      .ok (.call callee (readOnlyArguments [left, right]) [] memory) := by
    simp [step, cil_guard, observerCount, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, child⟩ ⟨1, returnTrace⟩
  refine ⟨fuel + 4, ?_⟩
  have vectorOn : profile.evaluate .vector256Accelerated = true := vector
  cil_checked_steps 4 [body, readOnlyArguments, fl, fr, vectorOn]
  exact tail

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (ReferenceVector.body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile callee)
    (fun left right => .i32 (if left = right then 1 else 0)) found
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit])
    (executed profile program index callee vector found leafFound) memory left right call

#print axioms executed
#print axioms checked
end UInt256Proof.Equality.ReferenceVectorWrapper
