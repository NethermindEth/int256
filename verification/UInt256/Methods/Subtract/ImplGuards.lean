import UInt256.Methods.Subtract.AcceleratedContract
import UInt256.Methods.Subtract.SegmentFetch

namespace UInt256Proof.Subtract.Profile
open CIL.Safety

/-- SubtractImpl with AVX2 disabled: an AVX2 guard, `k` unreachable placeholders, then the scalar dispatcher. -/
def subtractImplBodyWith (profile : CIL.FeatureProfile) (scalarIndex : Nat) (guard : List CIL.Op) (k : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.v256 0, .v256 0, .v256 0, .v256 0, .v256 0, .v256 0, .i32 0, .i32 0, .v256 0],
    localKinds := [.vector256, .vector256, .vector256, .vector256, .vector256, .vector256, .word32, .word32, .vector256],
    parameterHomes := [], staticSites := [],
    code := guard ++ List.replicate k subtractScalarUnreachable ++
      [.arg 0, .arg 1, .arg 2, .call scalarIndex 3, .ret (some .unsigned8)] ++ [] }

/-- The single feature test of the production shape. -/
def avx2Guard (k : Nat) : List CIL.Op := [.feature .avx2, .brzero (2 + k)]

/-- The same AVX2 test written as a feature conjunction with itself. -/
def avx2RepeatedGuard (k : Nat) : List CIL.Op := [.feature .avx2, .feature .avx2, .band, .brzero (4 + k)]

/-- A guard that, without AVX2, falls through to the scalar call site without touching memory. -/
def ImplGuardSkips (program : CIL.Program) (method : Nat) (guard : List CIL.Op) (k : Nat) : Prop :=
  ∀ args frame memory (post : Memory → List Value → Prop),
    (∃ fuel final values,
      run program fuel method (guard.length + k) args frame [] memory = .ok (final, values) ∧ post final values) →
    ∃ fuel final values, run program fuel method 0 args frame [] memory = .ok (final, values) ∧ post final values

theorem avx2_guard_skips (program : CIL.Program) (method scalarIndex k : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractImplBodyWith profile scalarIndex (avx2Guard k) k))
    (noAvx2 : profile.avx2 = false) : ImplGuardSkips program method (avx2Guard k) k := by
  intro args frame memory post continuation
  have bodyProfile : (subtractImplBodyWith profile scalarIndex (avx2Guard k) k).profile = profile := rfl
  apply run_next_exists post found (by rfl) (by
    simp [step, bodyProfile, noAvx2, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  apply run_next_exists post found (by rfl) (by
    simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  exact continuation

theorem avx2_repeated_guard_skips (program : CIL.Program) (method scalarIndex k : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractImplBodyWith profile scalarIndex (avx2RepeatedGuard k) k))
    (noAvx2 : profile.avx2 = false) : ImplGuardSkips program method (avx2RepeatedGuard k) k := by
  intro args frame memory post continuation
  have bodyProfile : (subtractImplBodyWith profile scalarIndex (avx2RepeatedGuard k) k).profile = profile := rfl
  iterate 2
    apply run_next_exists post found (by rfl) (by
      simp [step, bodyProfile, noAvx2, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
        Bind.bind, Except.bind, Pure.pure, Except.pure]; try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  apply run_next_exists post found (by rfl) (by
    simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  apply run_next_exists post found (by rfl) (by
    simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  exact continuation

#print axioms avx2_guard_skips
#print axioms avx2_repeated_guard_skips
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- SubtractImpl with a skipping guard forwards the dispatcher's exact result. -/
theorem subtract_impl_contract_with (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile)
    (guard : List CIL.Op) (k : Nat)
    (found : program[method]? = some (subtractImplBodyWith profile scalarIndex guard k))
    (skips : ImplGuardSkips program method guard k)
    (scalarChecked : ∀ memory left right output,
      CallingConditions program memory [left, right] [output] →
      ∃ fuel final values,
        invoke program fuel scalarIndex (binaryArguments left right output) memory = .ok (final, values) ∧
        SubtractResult memory final values left right output) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program method := by
  intro memory left right output call
  have fits : FrameSetupFits (subtractImplBodyWith profile scalarIndex guard k) (binaryArguments left right output) := by
    simp [subtractImplBodyWith, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit,
      ParameterArgumentsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, values, invoked, result⟩ := scalarChecked entered left right output enteredCall
  have flagEq := result.flag
  subst flagEq
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := output) (by simp)
  have code : (subtractImplBodyWith profile scalarIndex guard k).code =
      (guard ++ List.replicate k subtractScalarUnreachable) ++
        [.arg 0, .arg 1, .arg 2, .call scalarIndex 3, .ret (some .unsigned8)] ++ [] := rfl
  have leadingLength : (guard ++ List.replicate k subtractScalarUnreachable).length = guard.length + k := by simp
  have stepped : step (subtractImplBodyWith profile scalarIndex guard k) (.call scalarIndex 3) (guard.length + k + 3)
      (binaryArguments left right output) frame
      [.reference (.address output), .reference (.address right), .reference (.address left)]
      entered = .ok (.call scalarIndex (binaryArguments left right output) [] entered) := by
    simp [step, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found (by seg_fetch code leadingLength) stepped ⟨childFuel, invoked⟩
    ⟨1, subtract_flag_return program method _ (guard.length + k + 4) found rfl (by seg_fetch code leadingLength)
      _ frame after entered entered left right⟩
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame after ∧ values = [.scalar (.i32 (subtractUnderflow entered left right))]
  have guarded : ∃ fuel final values,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (final, values) ∧ post final values := by
    apply skips _ frame entered post
    exact subtract_forward_prefix program method _ (guard.length + k) found (by seg_fetch code leadingLength)
      (by seg_fetch code leadingLength) (by seg_fetch code leadingLength) left right output frame entered
      enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ := guarded
  subst final
  subst values
  obtain ⟨flagSame, value, writable, footprint⟩ :=
    subtract_forward_result program _ memory entered after frame left right output _ call setup result
  rw [flagSame] at finished
  refine ⟨fuel, leaveFrame frame after, ?_, value, writable, footprint⟩
  simpa only [subtractUnderflow, decide_eq_true_eq] using
    certify_invocation _ _ _ _ _ _ _ _ _ _ found (subtract_checked_arguments program memory left right output call)
      setup live finished

#print axioms subtract_impl_contract_with
end UInt256Proof.Subtract.Profile
