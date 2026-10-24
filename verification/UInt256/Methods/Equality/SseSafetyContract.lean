import UInt256.Methods.Equality.HalfSafetyFacts
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.GuardNormalization
namespace UInt256Proof.Equality.Safety
open CIL.Safety UInt256Model.Safety
 theorem intrinsic_equal128 (a b : BitVec 128) : CIL.evalIntrinsic (.vector (.equalsAll 128)) [.v128 a,.v128 b] = some (.i32 (if a = b then 1 else 0)) := by
  change some (CIL.Value.i32 (if a == b then 1 else 0)) = _
  simp
 theorem intrinsic_xor128 (a b : BitVec 128) : CIL.evalIntrinsic (.vector (.bxor 128)) [.v128 a,.v128 b] = some (.v128 (a ^^^ b)) := rfl
 theorem intrinsic_or128 (a b : BitVec 128) : CIL.evalIntrinsic (.vector (.bor 128)) [.v128 a,.v128 b] = some (.v128 (a ||| b)) := rfl
 theorem intrinsic_zero128 : CIL.evalIntrinsic (.vector (.zero 128)) [] = some (.v128 0) := rfl
private theorem s_arg {body : CIL.Method} {pc i : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {m : Memory} {r : Reference}
    (h : args[i]? = some (.reference (.address r))) (formed : form m r = .ok r) :
    step body (.arg i) pc args frame stack m = .ok (.next (pc + 1) (.reference (.address r) :: stack) frame m) := by
  unfold step
  simp only [cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, h, checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

private theorem s_asRef {body : CIL.Method} {pc : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m : Memory} {r : Reference} (formed : form m r = .ok r) :
    step body (.memory .asRef) pc args frame (.reference (.address r) :: rest) m =
      .ok (.next (pc + 1) (.reference (.address r) :: rest) frame m) := by
  unfold step staticInstruction memoryInstruction
  simp only [cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem s_setLocal {body : CIL.Method} {pc i : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m : Memory} {r : Reference} {old : Option ManagedReference}
    (slot : frame.locals[i]? = some (.root old)) (formed : form m r = .ok r) :
    step body (.setLocal i) pc args frame (.reference (.address r) :: rest) m =
      .ok (.next (pc + 1) rest { frame with locals := frame.locals.set i (.root (some (.address r))) } m) := by
  unfold step storeLocal
  simp only [cil_guard, observerCount, Bool.or_false, Bool.false_and, Bool.false_eq_true, ite_false, slot, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem s_local {body : CIL.Method} {pc i : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {m : Memory} {r : Reference}
    (slot : frame.locals[i]? = some (.root (some (.address r)))) (formed : form m r = .ok r) :
    step body (.local i) pc args frame stack m =
      .ok (.next (pc + 1) (.reference (.address r) :: stack) frame m) := by
  unfold step loadLocal
  simp only [cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, slot, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem s_load128 {body : CIL.Method} {pc : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m : Memory} {r : ManagedReference} {v : CIL.Value}
    (loaded : loadValue m r 16 = .ok v) :
    step body (.memory .load128) pc args frame (.reference r :: rest) m =
      .ok (.next (pc + 1) (.scalar v :: rest) frame m) := by
  unfold step staticInstruction memoryInstruction
  simp only [cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, loaded, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem s_add {body : CIL.Method} {pc size : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m : Memory} {r result : Reference} {offset : BitVec 32} {delta : BitVec 64}
    (converted : BitVec.ofInt 64 offset.toInt = delta) (added : add m r size delta = .ok result) :
    step body (.memory (.add size true)) pc args frame (.scalar (.i32 offset) :: .reference (.address r) :: rest) m =
      .ok (.next (pc + 1) (.reference (.address result) :: rest) frame m) := by
  unfold step staticInstruction memoryInstruction
  simp only [cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, ite_false, CIL.offsetValue, referenceAt, converted, added, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

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
  refine (run_next found rfl (s_arg (by rfl) fl)).trans ?_
  refine (run_next found rfl (s_asRef fl)).trans ?_
  refine (run_next found rfl (s_asRef fl)).trans ?_
  refine (run_next found rfl (s_setLocal rfl fl)).trans ?_
  refine (run_next found rfl (s_arg (by rfl) fr)).trans ?_
  refine (run_next found rfl (s_asRef fr)).trans ?_
  refine (run_next found rfl (s_asRef fr)).trans ?_
  refine (run_next found rfl (s_setLocal rfl fr)).trans ?_
  refine (run_next found rfl (s_local rfl fl)).trans ?_
  refine (run_next found rfl (s_load128 (hl 0))).trans ?_
  refine (run_next found rfl (s_local rfl fr)).trans ?_
  refine (run_next found rfl (s_load128 (hr 0))).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (s_local rfl fl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (s_add (by decide) (al 1))).trans ?_
  refine (run_next found rfl (s_load128 (hl 1))).trans ?_
  refine (run_next found rfl (s_local rfl fr)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (s_add (by decide) (ar 1))).trans ?_
  refine (run_next found rfl (s_load128 (hr 1))).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_return found rfl rfl rfl).trans ?_
  simp [leaveFrame, CIL.NarrowKind.extend, ← difference]
  split <;> rfl
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
