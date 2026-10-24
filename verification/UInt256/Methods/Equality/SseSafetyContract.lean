import UInt256.Methods.Equality.HalfSafetyFacts
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.GuardNormalization
import CIL.Safety.SymbolicExecution
namespace UInt256Proof.Equality.Safety
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
  .memory .load128,
  .local 1,
  .memory .load128,
  .intrinsic (.vector (.bxor 128)) 2,
  .local 0,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .local 1,
  .const32 1,
  .memory (.add 16 true),
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
  have difference := input_half_difference_zero memory left right
  obtain ⟨activation, frameLocals, owned, arguments⟩ := frame
  change frameLocals = _ at locals
  subst locals
  refine ⟨26, ?_⟩
  cil_checked_steps [readOnlyArguments, fl, fr, hl, hr, al, ar, staticInstruction, memoryInstruction, formValue,
    storeLocal, loadLocal, CIL.offsetValue, referenceAt]
  simp [CIL.NarrowKind.extend, ← difference]
#print axioms sse_run
end UInt256Proof.Equality.Safety





namespace UInt256Proof.Equality.Safety
open CIL.Safety UInt256Model.Safety
theorem sse_frame_fits (profile : CIL.FeatureProfile) (left right : Reference) :
    FrameSetupFits (body profile) (readOnlyArguments [left, right]) := by

  simp [body, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit]

theorem sse_frame_roots (profile : CIL.FeatureProfile) (memory : Memory) (left right : Reference)
    (frame : Frame) (entered : Memory)
    (setup : enterFrame (body profile) (readOnlyArguments [left, right]) memory = .ok (frame, entered)) :
    frame.locals = [.root (some .null), .root (some .null)] := by

  simp [body, enterFrame, makeSelectedLocals, makeLocals, makeLocal, makeArgumentHomes, makeParameterHomes,
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

end UInt256Proof.Equality.Safety
