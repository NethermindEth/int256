import UInt256.Methods.Add.ARMContract
import UInt256.Safety.ReportingContract
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Public AddOverflow without AVX2: call the scalar dispatcher with detectOverflow set and return its byte. -/
def publicReportingBody (profile : CIL.FeatureProfile) (scalarIndex : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.v256 0, .v256 0, .v256 0, .v256 0], localKinds := [.vector256, .vector256, .vector256, .vector256], parameterHomes := [], staticSites := [], code := [
  .feature .avx2,
  .brzero 28,
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
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .arg 0,
  .arg 1,
  .arg 2,
  .const32 1,
  .call scalarIndex 4,
  .ret (some .unsigned8)] }

theorem reporting_entry_prefix (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (publicReportingBody profile scalarIndex)) (disabled : profile.avx2 = false) (left right output : Reference) (frame : Frame) (memory : CIL.Safety.Memory)
  (call : CallingConditions program memory [left, right] [output])
  (post : CIL.Safety.Memory → List Value → Prop)
  (continuation : ∃ fuel final values,
    run program fuel method 32 (binaryArguments left right output)
      frame [.scalar (.i32 1), .reference (.address output), .reference (.address right),
        .reference (.address left)] memory = .ok (final, values) ∧ post final values) :
  ∃ fuel final values,
    run program fuel method 0 (binaryArguments left right output)
      frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · simp only [found, publicReportingBody, disabled]; rfl
      · simp only [found, publicReportingBody, disabled]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [found, publicReportingBody, disabled, binaryArguments, step, checkedValue, numericValue, formValue, fl, fr, fo,
            pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The byte return keeps an already normalized flag. -/
theorem reporting_entry_return (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (publicReportingBody profile scalarIndex)) (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : CIL.Safety.Memory)
    (normalized : CIL.NarrowKind.unsigned8.extend flag = flag) :
    run program 1 method (32 + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have returned : (publicReportingBody profile scalarIndex).code[32 + 1]? = some (.ret (some .unsigned8)) := by rfl
  have returns : (publicReportingBody profile scalarIndex).returnsValue = true := by rfl
  simp [run, found, returned, returns, step, normalized, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Public AddOverflow through its scalar dispatcher: exact initial-input carry, modular sum, writable output, caller bytes kept. -/
theorem add_overflow_contract_of_scalar (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (publicReportingBody profile scalarIndex)) (disabled : profile.avx2 = false)
    (child : ∀ memory left right output,
      CallingConditions program memory [left, right] [output] →
      ∃ fuel final returned,
        InvocationCertificate program scalarIndex
          (binaryArguments left right output ++ [.scalar (.i32 1)]) memory fuel final returned ∧
        ARMScalarReportingPost memory final returned left right output 1) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program method := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds
    (body := publicReportingBody profile scalarIndex)
    (by simp [publicReportingBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit])
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have leftSame := call.input_value_after_setup setup (by simp : left ∈ [left, right])
  have rightSame := call.input_value_after_setup setup (by simp : right ∈ [left, right])
  obtain ⟨childFuel, after, returned, certified, result⟩ := child entered left right output enteredCall
  let bit : BitVec 32 :=
    if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0
  have flagged : returned = [.scalar (.i32 bit)] := by
    have reported := result.overflow (by decide)
    rw [leftSame, rightSame] at reported
    exact reported
  subst returned
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := output) (by simp)
  have fetched : (publicReportingBody profile scalarIndex).code[32]? = some (.call scalarIndex 4) := by rfl
  have stepped : step (publicReportingBody profile scalarIndex) (.call scalarIndex 4) 32
      (binaryArguments left right output) frame
      [.scalar (.i32 1), .reference (.address output), .reference (.address right), .reference (.address left)] entered =
        .ok (.call scalarIndex (binaryArguments left right output ++ [.scalar (.i32 1)]) [] entered) := by
    simp [step, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certified.1⟩
    ⟨1, reporting_entry_return program method scalarIndex profile found (binaryArguments left right output)
      bit frame after (by simp only [bit]; split <;> rfl)⟩
  let post : CIL.Safety.Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame after ∧ values = [.scalar (.i32 bit)]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    reporting_entry_prefix program method scalarIndex profile found disabled left right output frame entered
      enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have sum := result.value
  rw [leftSame, rightSame] at sum
  have retired := arm_scalar_retire memory entered after frame left right output [.scalar (.i32 bit)]
    call preserved fresh.1.next (fun id member => (fresh.2 id member).1)
    result.wellFormed sum result.scalar result.writable result.footprint
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, leaveFrame frame after, ?_, retired.value, retired.writable, retired.footprint⟩
  simpa only [bit, decide_eq_true_eq] using
    certify_invocation program method (publicReportingBody profile scalarIndex)
      (binaryArguments left right output) memory frame entered fuel _ _ found checked setup live finished

theorem checked_arm_add_overflow_contract (program : CIL.Program) (entry scalar vector small storage : Nat)
    (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true) (disabled : profile.avx2 = false)
    (entryFound : program[entry]? = some (publicReportingBody profile scalar))
    (scalarFound : program[scalar]? = some (armScalarBody profile vector small))
    (vectorFound : program[vector]? = some (armBody profile))
    (smallFound : program[small]? = some (armSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program entry := by
  apply add_overflow_contract_of_scalar program entry scalar profile entryFound disabled
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    checked_arm_scalar_contract program scalar vector small storage profile scalarFound vectorFound smallFound storageFound enabled
      memory left right output 1 rfl call

#print axioms reporting_entry_prefix
#print axioms reporting_entry_return
#print axioms add_overflow_contract_of_scalar
#print axioms checked_arm_add_overflow_contract
end UInt256Proof.Add.Safety
